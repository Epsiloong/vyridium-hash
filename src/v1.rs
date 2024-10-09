// Public crates.
use chacha20::{cipher::KeyIvInit, ChaCha20};
use rc4::{Rc4, KeyInit, StreamCipher};
use sha2::{Sha512, Digest};
use blake3::hash as blake3_hash;
use siphasher::sip::SipHasher24;
use std::hash::Hasher;

use crate::{Error, Hash, HASH_SIZE};

// This is the maximum of the scratchpad.
const MAX_LENGTH: u32 = (256 * 384) - 1;
// Number of unique operations
// const OP_COUNT: u64 = 256;
// Number of operations per branch
const OP_PER_BRANCH: u64 = 8;
const MEMORY_SIZE: usize = 1572864;
const CHUNK_SIZE: usize = 32;
const NONCE_SIZE: usize = 12;
const OUTPUT_SIZE: usize = MEMORY_SIZE / 8;
const LCG_MUL: usize = 1664525;    // LCG multiplier
const LCG_INC: usize = 1013904223; // LCG increment
const PRIME_MUL: usize = 2654435761;

// Generate cachehog
fn populate_cachehog(input: &[u8]) -> Result<[u8; MEMORY_SIZE], Error> {
    let mut cachehog = [0u8; MEMORY_SIZE];

    let mut output_offset = 0;
    let mut nonce = [0u8; NONCE_SIZE];

    // Generate the nonce from the input
    let mut input_hash: Hash = blake3_hash(input).into();
    nonce.copy_from_slice(&input_hash[..NONCE_SIZE]);

    let num_chunks = (input.len() + CHUNK_SIZE - 1) / CHUNK_SIZE;

    for (chunk_index, chunk) in input.chunks(CHUNK_SIZE).enumerate() {
        // Concatenate the input hash with the chunk
        let mut tmp = [0u8; HASH_SIZE * 2];
        tmp[0..HASH_SIZE].copy_from_slice(&input_hash);
        tmp[HASH_SIZE..HASH_SIZE + chunk.len()].copy_from_slice(chunk);

        // Hash it to not trust the input
        input_hash = blake3_hash(&tmp).into();

        let mut cipher = ChaCha20::new(&input_hash.into(), &nonce.into());

        // Calculate the remaining size and how much to generate this iteration
        let remaining_output_size = OUTPUT_SIZE - output_offset;
        // Remaining chunks
        let chunks_left = num_chunks - chunk_index;
        let chunk_output_size = remaining_output_size / chunks_left;
        let current_output_size = remaining_output_size.min(chunk_output_size);

        // Apply the keystream to the output
        let offset = chunk_index * current_output_size;
        let part = &mut cachehog[offset..offset+current_output_size];
        cipher.apply_keystream(part);

        output_offset += current_output_size;

        // Update the nonce with the last NONCE_SIZE bytes of temp_output
        let nonce_start = current_output_size.saturating_sub(NONCE_SIZE);

        // Copy the new nonce
        nonce.copy_from_slice(&part[nonce_start..]);
    }

    Ok(cachehog)
}

// Generate branch table
fn populate_branch_table(input: &[u8]) -> [u64; 4096] {
    let mut output: [u8; 32768] = [0; 32768];
    let mut hasher = Sha512::new();

    hasher.update(input);

    let mut last_hash: [u8; 64];
    let mut hash_idx = 0;
    while hash_idx < 512 {
        last_hash = hasher.finalize_reset().into();
        output[hash_idx * 64..(hash_idx + 1) * 64].copy_from_slice(last_hash.as_ref());
        // Add some variation so it's not just a chained hash
        for item in last_hash.iter_mut() {
            *item = item.wrapping_mul(5);
        }
        hasher.update(last_hash);
        hash_idx += 1;
    }

    let output_u64: [u64; 4096] = unsafe { std::mem::transmute(output) };

    output_u64
}

// Encrypt and return salsa20 stream.
fn chacha20_calc(key: &[u8; 32]) -> [u8; 256] {
    let mut output: [u8; 256] = [0; 256];
    let mut cipher = ChaCha20::new(key.into(), &[0; 12].into());
    cipher.apply_keystream(&mut output);
    output
}

// Calculate and return fnv1a hash.
fn fnv1a_calc(input: &[u8]) -> u64 {
    let mut hasher = fnv::FnvHasher::default();
    hasher.write(input);
    hasher.finish()
}

// Calculate and return xxh64 hash.
fn xxh3_calc(input: &[u8], seed: u64) -> u64 {
    xxhash_rust::xxh3::xxh3_64_with_seed(input, seed)
}

// Calculate and return sip24 hash.
fn sip24_calc(input: &[u8], k0: u64, k1: u64) -> u64 {
    let hasher = SipHasher24::new_with_keys(k0, k1);

    hasher.hash(input)
}

pub fn vyridium_hash(input: &[u8]) -> Result<Hash, Error> {
    let branch_table = populate_branch_table(input);

    let mut hashhog_bytes = populate_cachehog(input)?;
    

    // Step 1+2: calculate blake3 and expand data using chacha20.
    let mut data: [u8; 256] = chacha20_calc(&(blake3_hash(input).into()));

    // Step 3: rc4.
    let mut rc4 = Rc4::new(&data.into());
    let mut stream = data.to_vec();
    rc4.apply_keystream(&mut stream);
    data.copy_from_slice(&stream);

    // Step 4: fnv1a.
    let mut lhash = fnv1a_calc(&data);

    // Step 5: branchy loop to avoid GPU/FPGA optimizations.
    let mut scratch_data = [0u8; (MAX_LENGTH + 64) as usize];
    let mut prev_lhash = lhash;
    let mut tries: u64 = 0;

    loop {
        tries += 1;
        let random_switcher = xxh3_calc(&[(prev_lhash ^ lhash) as u8], tries);
        let branch: u32 = random_switcher as u32 % (branch_table.len() as u32);
        let mut pos1: u8 = random_switcher.wrapping_shr(8) as u8;
        let mut pos2: u8 = random_switcher.wrapping_shr(16) as u8;

        // Insure pos2 is larger.
        if pos1 > pos2 {
            std::mem::swap(&mut pos1, &mut pos2);
        }

        // Bounds check elimination.
        let _ = &data[pos1 as usize..pos2 as usize];

        // Get list of operations for a given branch
        let opcode = branch_table[branch as usize];
        if let 0..=511 = branch {
            // Use a new key.
            rc4 = Rc4::new(&data.into());
        }
        // Run operations on data i number of times
        for i in pos1..pos2 {
            let mut tmp = data[i as usize];
            for j in (0..OP_PER_BRANCH).rev() {
                let intermediate = (tmp as usize).wrapping_add(data[i.wrapping_sub(tmp) as usize] as usize).wrapping_add(j as usize).wrapping_mul(i  as usize);
                let lcg_value = LCG_MUL.wrapping_mul(intermediate).wrapping_add(LCG_INC);
                let cachehog_idx = lcg_value * PRIME_MUL % hashhog_bytes.len();
                let op = (opcode >> (j * 8)) & 0xFF;
                tmp = match op {
                    0x00 => ((tmp >> 4) | (tmp & 0x0F) ^ 0b0101).wrapping_sub(hashhog_bytes[cachehog_idx]), // invert odd bits right nibble
                    0x01 => (tmp ^ 0b10101010).wrapping_add(hashhog_bytes[cachehog_idx]), // invert even bits
                    0x02 => ((tmp >> 4) | (tmp & 0x0F) ^ 0b1010).wrapping_mul(hashhog_bytes[cachehog_idx]), // invert even bits right nibble
                    0x03 => tmp.wrapping_shl((tmp & 3) as u32).wrapping_mul(hashhog_bytes[cachehog_idx]),              // shift left
                    0x04 => tmp.wrapping_mul(tmp) ^ hashhog_bytes[cachehog_idx],                                 // *
                    0x05 => ((tmp >> 4) | (tmp & 0x0F).rotate_right(tmp as u32)) ^ hashhog_bytes[cachehog_idx], // rotate random bits right nibble
                    0x06 => ((tmp >> 4) ^ data[pos2 as usize] | (tmp & 0x0F)).wrapping_mul(hashhog_bytes[cachehog_idx]), // left nibble XOR with end of data
                    0x07 => tmp & data[pos2 as usize] ^ hashhog_bytes[cachehog_idx], // AND with end of data
                    0x08 => tmp ^ data[pos2 as usize] ^ hashhog_bytes[cachehog_idx], // XOR with end of data
                    0x09 => tmp.wrapping_sub((tmp.leading_zeros() as u8).wrapping_mul(43)) ^ hashhog_bytes[cachehog_idx],
                    0x0A => ((tmp >> 4) | (tmp & 0x0F).reverse_bits()).wrapping_mul(hashhog_bytes[cachehog_idx]), // reverse right nibble
                    0x0B => ((tmp >> 4) | (tmp & 0x0F) ^ 0b0101) ^ hashhog_bytes[cachehog_idx], // invert odd bits right nibble
                    0x0C => ((tmp >> 4) | (tmp & 0x0F).rotate_left(1)).wrapping_add(hashhog_bytes[cachehog_idx]), // rotate left 1 bits right nibble
                    0x0D => tmp.wrapping_add(tmp).wrapping_add(hashhog_bytes[cachehog_idx]),                                 // +
                    0x0E => ((tmp >> 4) | (tmp & 0x0F).wrapping_add(tmp)).wrapping_mul(hashhog_bytes[cachehog_idx]),     // right nibble +
                    0x0F => tmp.rotate_right(5).wrapping_sub(hashhog_bytes[cachehog_idx]),                             // rotate right 5
                    0x10 => tmp.reverse_bits().wrapping_mul(hashhog_bytes[cachehog_idx]),                              // reverse bits
                    0x11 => tmp.rotate_left(tmp as u32) ^ hashhog_bytes[cachehog_idx],                     // rotate left random
                    0x12 => tmp.rotate_left(7).wrapping_add(hashhog_bytes[cachehog_idx]),                              // rotate left 7
                    0x13 => tmp.rotate_left(1).wrapping_mul(hashhog_bytes[cachehog_idx]),                              // rotate left 1
                    0x14 => tmp.wrapping_mul((tmp.count_zeros() as u8).wrapping_add(1)).wrapping_add(hashhog_bytes[cachehog_idx]),
                    0x15 => ((tmp >> 4) | (tmp & 0x0F).rotate_left(tmp as u32)).wrapping_sub(hashhog_bytes[cachehog_idx]), // rotate left random right nibble
                    0x16 => tmp.rotate_right(1).wrapping_mul(hashhog_bytes[cachehog_idx]),                             // rotate right 1
                    0x17 => tmp.wrapping_mul(tmp).wrapping_add(hashhog_bytes[cachehog_idx]),                                 // *
                    0x18 => tmp.rotate_left(tmp as u32).wrapping_sub(hashhog_bytes[cachehog_idx]),                     // rotate left random
                    0x19 => tmp & data[pos2 as usize].wrapping_sub(hashhog_bytes[cachehog_idx]), // AND with end of data
                    0x1A => ((tmp >> 4) | (tmp << 4)).wrapping_mul(hashhog_bytes[cachehog_idx]),                       // swap nibbles
                    0x1B => tmp.wrapping_shr((tmp & 3) as u32).wrapping_add(hashhog_bytes[cachehog_idx]),              // shift right
                    0x1C => ((tmp >> 4).reverse_bits() | (tmp & 0x0F)).wrapping_add(hashhog_bytes[cachehog_idx]), // reverse left nibble
                    0x1D => tmp ^ tmp.rotate_left(2).wrapping_mul(hashhog_bytes[cachehog_idx]),                        // rotate left 2, XOR
                    0x1E => tmp ^ tmp.rotate_left(2).wrapping_add(hashhog_bytes[cachehog_idx]),                        // rotate left 2, XOR
                    0x1F => (((tmp >> 1) & 0b01010101) | ((tmp << 1) & 0b10101010)) ^ hashhog_bytes[cachehog_idx], // swap adjacent bits
                    0x20 => tmp.rotate_right(tmp as u32).wrapping_mul(hashhog_bytes[cachehog_idx]),                    // rotate right random
                    0x21 => ((tmp >> 4).rotate_left(tmp as u32) | (tmp & 0x0F)).wrapping_mul(hashhog_bytes[cachehog_idx]), // rotate left random left nibble
                    0x22 => ((tmp >> 4).rotate_left(1) | (tmp & 0x0F)) ^ hashhog_bytes[cachehog_idx], // rotate left 1 left nibble
                    0x23 => ((tmp >> 4).rotate_right(tmp as u32) | (tmp & 0x0F)).wrapping_mul(hashhog_bytes[cachehog_idx]), // rotate random left nibble
                    0x24 => tmp.rotate_left(tmp as u32).wrapping_mul(hashhog_bytes[cachehog_idx]),                     // rotate left random
                    0x25 => tmp ^ tmp.rotate_left(2).wrapping_sub(hashhog_bytes[cachehog_idx]),                        // rotate left 2, XOR
                    0x26 => tmp.rotate_right(tmp as u32).wrapping_add(hashhog_bytes[cachehog_idx]),                    // rotate right random
                    0x27 => tmp ^ tmp.rotate_right(2).wrapping_mul(hashhog_bytes[cachehog_idx]),                       // rotate right 2, XOR
                    0x28 => !tmp ^ hashhog_bytes[cachehog_idx],                                            // binary NOT operator
                    0x29 => ((tmp >> 4).rotate_right(tmp as u32) | (tmp & 0x0F)) ^ hashhog_bytes[cachehog_idx], // rotate random left nibble
                    0x2A => tmp.wrapping_mul(tmp).wrapping_mul(hashhog_bytes[cachehog_idx]),                                 // *
                    0x2B => tmp.rotate_left(5).wrapping_mul(hashhog_bytes[cachehog_idx]),                              // rotate left 5
                    0x2C => tmp.reverse_bits().wrapping_add(hashhog_bytes[cachehog_idx]),                              // reverse bits
                    0x2D => ((tmp >> 4) | (tmp & 0x0F).rotate_left(1)).wrapping_sub(hashhog_bytes[cachehog_idx]), // rotate left 1 bits right nibble
                    0x2E => tmp.wrapping_mul(data[pos1 as usize]).wrapping_mul(hashhog_bytes[cachehog_idx]), // * with beginning of data
                    0x2F => tmp ^ tmp.rotate_right(6).wrapping_sub(hashhog_bytes[cachehog_idx]),                       // rotate right 6, XOR
                    0x30 => ((tmp >> 4) ^ data[pos2 as usize] | (tmp & 0x0F)).wrapping_add(hashhog_bytes[cachehog_idx]), // left nibble XOR with end of data
                    0x31 => tmp.rotate_right(1).wrapping_add(hashhog_bytes[cachehog_idx]),                             // rotate right 1
                    0x32 => tmp.rotate_left(5).wrapping_sub(hashhog_bytes[cachehog_idx]),                              // rotate left 5
                    0x33 => ((tmp >> 4) | (tmp & 0x0F) & data[pos2 as usize]) ^ hashhog_bytes[cachehog_idx], // right nibble AND with end of data
                    0x34 => tmp ^ tmp.rotate_right(4).wrapping_add(hashhog_bytes[cachehog_idx]),                       // rotate right 4, XOR
                    0x35 => ((tmp >> 4).reverse_bits() | (tmp & 0x0F)).wrapping_mul(hashhog_bytes[cachehog_idx]), // reverse left nibble
                    0x36 => ((tmp >> 4).rotate_left(3) | (tmp & 0x0F)) ^ hashhog_bytes[cachehog_idx], // rotate left 3 bits left nibble
                    0x37 => ((tmp >> 4) & data[pos2 as usize] | (tmp & 0x0F)).wrapping_add(hashhog_bytes[cachehog_idx]), // left nibble AND with end of data
                    0x38 => ((tmp >> 4).rotate_left(3) | (tmp & 0x0F)).wrapping_mul(hashhog_bytes[cachehog_idx]), // rotate left 3 bits left nibble
                    0x39 => tmp.wrapping_add(tmp).wrapping_mul(hashhog_bytes[cachehog_idx]),                                 // +
                    0x3A => ((tmp >> 4) | (tmp & 0x0F).wrapping_add(tmp)) ^ hashhog_bytes[cachehog_idx],     // right nibble +
                    0x3B => ((tmp >> 4) | (tmp & 0x0F).rotate_left(tmp as u32)) ^ hashhog_bytes[cachehog_idx], // rotate left random right nibble
                    0x3C => tmp ^ data[(pos2 as usize + pos1 as usize) / 2].wrapping_mul(hashhog_bytes[cachehog_idx]), // AND with midpoint of data
                    0x3D => tmp.wrapping_mul(tmp).wrapping_sub(hashhog_bytes[cachehog_idx]),                                 // *
                    0x3E => tmp & data[pos2 as usize].wrapping_mul(hashhog_bytes[cachehog_idx]), // AND with end of data
                    0x3F => tmp ^ tmp.rotate_right(2) ^ hashhog_bytes[cachehog_idx],                       // rotate right 2, XOR
                    0x40 => tmp.wrapping_sub(tmp ^ 97).wrapping_add(hashhog_bytes[cachehog_idx]),                            // XOR and
                    0x41 => tmp.rotate_left(1).wrapping_add(hashhog_bytes[cachehog_idx]),                              // rotate left 1
                    0x42 => tmp ^ tmp.rotate_right(2).wrapping_sub(hashhog_bytes[cachehog_idx]),                       // rotate right 2, XOR
                    0x43 => ((tmp >> 4).wrapping_mul(tmp) | (tmp & 0x0F)) ^ hashhog_bytes[cachehog_idx],     // left nibble *
                    0x44 => (tmp ^ tmp.count_ones() as u8).wrapping_mul(hashhog_bytes[cachehog_idx]),                    // ones count bits
                    0x45 => tmp ^ tmp.rotate_right(4) ^ hashhog_bytes[cachehog_idx],                       // rotate right 4, XOR
                    0x46 => ((tmp >> 4).rotate_left(3) | (tmp & 0x0F)).wrapping_add(hashhog_bytes[cachehog_idx]), // rotate left 3 bits left nibble
                    0x47 => tmp & data[pos1 as usize].wrapping_add(hashhog_bytes[cachehog_idx]), // AND with beginning of data
                    0x48 => ((tmp >> 4) | (tmp & 0x0F).rotate_right(1)).wrapping_mul(hashhog_bytes[cachehog_idx]), // rotate right 1 bits right nibble
                    0x49 => tmp.rotate_left(7).wrapping_sub(hashhog_bytes[cachehog_idx]),                              // rotate left 7
                    0x4A => ((tmp >> 4).wrapping_add(tmp) | (tmp & 0x0F)).wrapping_mul(hashhog_bytes[cachehog_idx]),     // left nibble +
                    0x4B => ((tmp >> 4) | (tmp & 0x0F).wrapping_add(tmp)).wrapping_add(hashhog_bytes[cachehog_idx]),     // right nibble +
                    0x4C => ((tmp >> 4).rotate_right(3) | (tmp & 0x0F)).wrapping_mul(hashhog_bytes[cachehog_idx]), // rotate right 3 bits left nibble
                    0x4D => tmp ^ data[(pos2 as usize + pos1 as usize) / 2].wrapping_sub(hashhog_bytes[cachehog_idx]), // AND with midpoint of data
                    0x4E => ((tmp >> 4).reverse_bits() | (tmp & 0x0F)) ^ hashhog_bytes[cachehog_idx], // reverse left nibble
                    0x4F => tmp.rotate_right(7).wrapping_add(hashhog_bytes[cachehog_idx]),                             // rotate right 7
                    0x50 => ((tmp >> 4) | (tmp & 0x0F).rotate_right(1)).wrapping_sub(hashhog_bytes[cachehog_idx]), // rotate right 1 bits right nibble
                    0x51 => tmp.wrapping_sub(tmp ^ 97).wrapping_mul(hashhog_bytes[cachehog_idx]),                            // XOR and
                    0x52 => ((tmp >> 4) | (tmp & 0x0F).rotate_right(3)).wrapping_add(hashhog_bytes[cachehog_idx]), // rotate right 3 bits right nibble
                    0x53 => ((tmp >> 4) | (tmp & 0x0F).rotate_right(3)).wrapping_mul(hashhog_bytes[cachehog_idx]), // rotate right 3 bits right nibble
                    0x54 => tmp ^ tmp.rotate_left(2) ^ hashhog_bytes[cachehog_idx],                        // rotate left 2, XOR
                    0x55 => tmp.wrapping_shr((tmp & 3) as u32).wrapping_sub(hashhog_bytes[cachehog_idx]),              // shift right
                    0x56 => tmp ^ data[(pos2 as usize + pos1 as usize) / 2].wrapping_add(hashhog_bytes[cachehog_idx]), // AND with midpoint of data
                    0x57 => ((tmp >> 4).rotate_right(1) | (tmp & 0x0F)).wrapping_mul(hashhog_bytes[cachehog_idx]), // rotate right 1 left nibble
                    0x58 => tmp ^ tmp.count_ones() as u8 ^ hashhog_bytes[cachehog_idx],                    // ones count bits
                    0x59 => tmp.wrapping_add(tmp.count_ones() as u8).wrapping_add(hashhog_bytes[cachehog_idx]),
                    0x5A => ((tmp >> 4) | (tmp & 0x0F).wrapping_mul(tmp)).wrapping_mul(hashhog_bytes[cachehog_idx]),     // right nibble *
                    0x5B => tmp.rotate_right(tmp as u32) ^ hashhog_bytes[cachehog_idx],                    // rotate right random
                    0x5C => ((tmp >> 4) | (tmp & 0x0F).reverse_bits()).wrapping_add(hashhog_bytes[cachehog_idx]), // reverse right nibble
                    0x5D => ((tmp >> 4).rotate_right(1) | (tmp & 0x0F)) ^ hashhog_bytes[cachehog_idx], // rotate right 1 left nibble
                    0x5E => tmp ^ data[pos1 as usize].wrapping_mul(hashhog_bytes[cachehog_idx]), // XOR with beginning of data
                    0x5F => ((tmp >> 4).rotate_right(3) | (tmp & 0x0F)).wrapping_add(hashhog_bytes[cachehog_idx]), // rotate right 3 bits left nibble
                    0x60 => ((tmp >> 4) | (tmp & 0x0F).rotate_right(1)).wrapping_add(hashhog_bytes[cachehog_idx]), // rotate right 1 bits right nibble
                    0x61 => tmp.wrapping_mul((tmp.trailing_ones() as u8).wrapping_add(7)).wrapping_add(hashhog_bytes[cachehog_idx]),
                    0x62 => tmp.rotate_right(1).wrapping_sub(hashhog_bytes[cachehog_idx]),                             // rotate right 1
                    0x63 => ((tmp >> 4).wrapping_mul(tmp) | (tmp & 0x0F)).wrapping_mul(hashhog_bytes[cachehog_idx]),     // left nibble *
                    0x64 => ((tmp >> 4) | (tmp & 0x0F).rotate_right(tmp as u32)).wrapping_add(hashhog_bytes[cachehog_idx]), // rotate random bits right nibble
                    0x65 => tmp & data[pos1 as usize].wrapping_mul(hashhog_bytes[cachehog_idx]), // AND with beginning of data
                    0x66 => ((tmp >> 4).reverse_bits() | (tmp & 0x0F)).wrapping_sub(hashhog_bytes[cachehog_idx]), // reverse left nibble
                    0x67 => tmp.wrapping_add(tmp).wrapping_sub(hashhog_bytes[cachehog_idx]),                                 // +
                    0x68 => ((tmp >> 4) | (tmp << 4)).wrapping_sub(hashhog_bytes[cachehog_idx]),                       // swap nibbles
                    0x69 => ((tmp >> 4).rotate_right(1) | (tmp & 0x0F)).wrapping_add(hashhog_bytes[cachehog_idx]), // rotate right 1 left nibble
                    0x6A => ((tmp >> 4) | (tmp & 0x0F).wrapping_mul(tmp)).wrapping_sub(hashhog_bytes[cachehog_idx]),     // right nibble *
                    0x6B => tmp.wrapping_mul((tmp.count_zeros() as u8).wrapping_add(1)) ^ hashhog_bytes[cachehog_idx],
                    0x6C => ((tmp >> 4).rotate_left(tmp as u32) | (tmp & 0x0F)).wrapping_sub(hashhog_bytes[cachehog_idx]), // rotate left random left nibble
                    0x6D => tmp ^ data[pos2 as usize].wrapping_sub(hashhog_bytes[cachehog_idx]), // XOR with end of data
                    0x6E => ((tmp >> 4) ^ data[pos2 as usize] | (tmp & 0x0F)).wrapping_sub(hashhog_bytes[cachehog_idx]), // left nibble XOR with end of data
                    0x6F => tmp.rotate_right(5).wrapping_mul(hashhog_bytes[cachehog_idx]),                             // rotate right 5
                    0x70 => ((tmp >> 4).rotate_left(tmp as u32) | (tmp & 0x0F)) ^ hashhog_bytes[cachehog_idx], // rotate left random left nibble
                    0x71 => ((tmp >> 4) ^ 0b1010 | (tmp & 0x0F)).wrapping_mul(hashhog_bytes[cachehog_idx]), // invert even bits left nibble
                    0x72 => tmp.rotate_right(tmp as u32).wrapping_sub(hashhog_bytes[cachehog_idx]),                    // rotate right random
                    0x73 => (tmp ^ tmp.count_ones() as u8).wrapping_add(hashhog_bytes[cachehog_idx]),                    // ones count bits
                    0x74 => tmp.rotate_right(5).wrapping_add(hashhog_bytes[cachehog_idx]),                             // rotate right 5
                    0x75 => tmp ^ tmp.rotate_right(6).wrapping_add(hashhog_bytes[cachehog_idx]),                       // rotate right 6, XOR
                    0x76 => ((tmp >> 4) ^ 0b0101 | (tmp & 0x0F)).wrapping_mul(hashhog_bytes[cachehog_idx]), // invert odd bits left nibble
                    0x77 => ((tmp >> 4) & data[pos2 as usize] | (tmp & 0x0F)).wrapping_mul(hashhog_bytes[cachehog_idx]), // left nibble AND with end of data
                    0x78 => ((tmp >> 4) | (tmp & 0x0F) & data[pos2 as usize]).wrapping_sub(hashhog_bytes[cachehog_idx]), // right nibble AND with end of data
                    0x79 => tmp.wrapping_shr((tmp & 3) as u32) ^ hashhog_bytes[cachehog_idx],              // shift right
                    0x7A => ((tmp >> 4).rotate_right(tmp as u32) | (tmp & 0x0F)).wrapping_add(hashhog_bytes[cachehog_idx]), // rotate random left nibble
                    0x7B => ((tmp >> 4) | (tmp & 0x0F) ^ 0b1010).wrapping_add(hashhog_bytes[cachehog_idx]), // invert even bits right nibble
                    0x7C => tmp & data[pos1 as usize].wrapping_sub(hashhog_bytes[cachehog_idx]), // AND with beginning of data
                    0x7D => tmp.rotate_left(1).wrapping_sub(hashhog_bytes[cachehog_idx]),                              // rotate left 1
                    0x7E => tmp.rotate_right(5) ^ hashhog_bytes[cachehog_idx],                             // rotate right 5
                    0x7F => (tmp ^ 0b01010101).wrapping_add(hashhog_bytes[cachehog_idx]), // invert odd bits
                    0x80 => ((tmp >> 4) ^ 0b1010 | (tmp & 0x0F)).wrapping_add(hashhog_bytes[cachehog_idx]), // invert even bits left nibble
                    0x81 => tmp.rotate_left(tmp as u32).wrapping_add(hashhog_bytes[cachehog_idx]),                     // rotate left random
                    0x82 => ((tmp >> 4) | (tmp << 4)).wrapping_add(hashhog_bytes[cachehog_idx]),                       // swap nibbles
                    0x83 => tmp.reverse_bits().wrapping_sub(hashhog_bytes[cachehog_idx]),                              // reverse bits
                    0x84 => ((tmp >> 4) | (tmp & 0x0F).rotate_left(tmp as u32)).wrapping_add(hashhog_bytes[cachehog_idx]), // rotate left random right nibble
                    0x85 => ((tmp >> 4) | (tmp & 0x0F).rotate_left(3)).wrapping_sub(hashhog_bytes[cachehog_idx]), // rotate left 3 bits right nibble
                    0x86 => (tmp ^ 0b01010101).wrapping_sub(hashhog_bytes[cachehog_idx]), // invert odd bits
                    0x87 => tmp.rotate_left(3).wrapping_sub(hashhog_bytes[cachehog_idx]),                              // rotate left 3
                    0x88 => ((tmp >> 4) | (tmp & 0x0F).rotate_left(3)).wrapping_add(hashhog_bytes[cachehog_idx]), // rotate left 3 bits right nibble
                    0x89 => (!tmp).wrapping_mul(hashhog_bytes[cachehog_idx]),                                            // binary NOT operator
                    0x8A => ((tmp >> 4) | (tmp & 0x0F) ^ data[pos2 as usize]) ^ hashhog_bytes[cachehog_idx], // right nibble XOR with end of data
                    0x8B => tmp.rotate_left(1) ^ hashhog_bytes[cachehog_idx],                              // rotate left 1
                    0x8C => tmp ^ tmp.rotate_left(4).wrapping_add(hashhog_bytes[cachehog_idx]),                        // rotate left 4, XOR
                    0x8D => ((tmp >> 4) | (tmp & 0x0F) ^ 0b0101).wrapping_mul(hashhog_bytes[cachehog_idx]), // invert odd bits right nibble
                    0x8E => tmp.wrapping_shr((tmp & 3) as u32).wrapping_mul(hashhog_bytes[cachehog_idx]),              // shift right
                    0x8F => tmp.rotate_right(3) ^ hashhog_bytes[cachehog_idx],                             // rotate right 3
                    0x90 => ((tmp >> 4) | (tmp & 0x0F).rotate_right(3)) ^ hashhog_bytes[cachehog_idx], // rotate right 3 bits right nibble
                    0x91 => tmp.wrapping_shl((tmp & 3) as u32) ^ hashhog_bytes[cachehog_idx],              // shift left
                    0x92 => ((tmp >> 4) | (tmp & 0x0F) ^ data[pos2 as usize]).wrapping_sub(hashhog_bytes[cachehog_idx]), // right nibble XOR with end of data
                    0x93 => tmp ^ data[(pos2 as usize + pos1 as usize) / 2] ^ hashhog_bytes[cachehog_idx], // AND with midpoint of data
                    0x94 => ((tmp >> 4) ^ 0b0101 | (tmp & 0x0F)) ^ hashhog_bytes[cachehog_idx], // invert odd bits left nibble
                    0x95 => ((tmp >> 4) | (tmp & 0x0F) ^ 0b1010).wrapping_sub(hashhog_bytes[cachehog_idx]), // invert even bits right nibble
                    0x96 => ((tmp >> 4) | (tmp & 0x0F) ^ data[pos2 as usize]).wrapping_add(hashhog_bytes[cachehog_idx]), // right nibble XOR with end of data
                    0x97 => ((tmp >> 4) | (tmp & 0x0F).wrapping_add(tmp)).wrapping_sub(hashhog_bytes[cachehog_idx]),     // right nibble +
                    0x98 => tmp.wrapping_add(tmp) ^ hashhog_bytes[cachehog_idx],                                 // +
                    0x99 => ((tmp >> 4) & data[pos2 as usize] | (tmp & 0x0F)).wrapping_sub(hashhog_bytes[cachehog_idx]), // left nibble AND with end of data
                    0x9A => tmp.rotate_left(3).wrapping_add(hashhog_bytes[cachehog_idx]),                              // rotate left 3
                    0x9B => tmp ^ tmp.rotate_left(4).wrapping_mul(hashhog_bytes[cachehog_idx]),                        // rotate left 4, XOR
                    0x9C => tmp.wrapping_sub((tmp.leading_zeros() as u8).wrapping_mul(43)).wrapping_add(hashhog_bytes[cachehog_idx]),
                    0x9D => tmp.rotate_right(3).wrapping_add(hashhog_bytes[cachehog_idx]),                             // rotate right 3
                    0x9E => ((tmp >> 4) | (tmp & 0x0F).rotate_right(3)).wrapping_sub(hashhog_bytes[cachehog_idx]), // rotate right 3 bits right nibble
                    0x9F => ((tmp >> 4) | (tmp & 0x0F) & data[pos2 as usize]).wrapping_mul(hashhog_bytes[cachehog_idx]), // right nibble AND with end of data
                    0xA0 => ((tmp >> 4) | (tmp << 4)) ^ hashhog_bytes[cachehog_idx],                       // swap nibbles
                    0xA1 => tmp.wrapping_mul(data[pos1 as usize]).wrapping_sub(hashhog_bytes[cachehog_idx]), // * with beginning of data
                    0xA2 => ((tmp >> 4).wrapping_add(tmp) | (tmp & 0x0F)).wrapping_add(hashhog_bytes[cachehog_idx]),     // left nibble +
                    0xA3 => (tmp ^ 0b10101010).wrapping_mul(hashhog_bytes[cachehog_idx]), // invert even bits
                    0xA4 => tmp ^ tmp.rotate_right(2).wrapping_add(hashhog_bytes[cachehog_idx]),                       // rotate right 2, XOR
                    0xA5 => ((tmp >> 4) | (tmp & 0x0F).rotate_right(tmp as u32)).wrapping_mul(hashhog_bytes[cachehog_idx]), // rotate random bits right nibble
                    0xA6 => tmp.wrapping_mul((tmp.trailing_ones() as u8).wrapping_add(7)).wrapping_sub(hashhog_bytes[cachehog_idx]),
                    0xA7 => tmp ^ tmp.rotate_left(6).wrapping_add(hashhog_bytes[cachehog_idx]),                        // rotate left 6, XOR
                    0xA8 => ((tmp >> 4) ^ 0b1010 | (tmp & 0x0F)) ^ hashhog_bytes[cachehog_idx], // invert even bits left nibble
                    0xA9 => ((tmp >> 4) | (tmp & 0x0F).rotate_left(tmp as u32)).wrapping_mul(hashhog_bytes[cachehog_idx]), // rotate left random right nibble
                    0xAA => tmp ^ tmp.rotate_left(6).wrapping_mul(hashhog_bytes[cachehog_idx]),                        // rotate left 6, XOR
                    0xAB => tmp.rotate_right(7).wrapping_mul(hashhog_bytes[cachehog_idx]),                             // rotate right 7
                    0xAC => (((tmp >> 1) & 0b01010101) | ((tmp << 1) & 0b10101010)).wrapping_mul(hashhog_bytes[cachehog_idx]), // swap adjacent bits
                    0xAD => tmp.wrapping_mul((tmp.trailing_ones() as u8).wrapping_add(7)).wrapping_mul(hashhog_bytes[cachehog_idx]),
                    0xAE => ((tmp >> 4) | (tmp & 0x0F) ^ 0b0101).wrapping_add(hashhog_bytes[cachehog_idx]), // invert odd bits right nibble
                    0xAF => ((tmp >> 4) | (tmp & 0x0F).rotate_right(tmp as u32)).wrapping_sub(hashhog_bytes[cachehog_idx]), // rotate random bits right nibble
                    0xB0 => tmp.rotate_left(7).wrapping_mul(hashhog_bytes[cachehog_idx]),                              // rotate left 7
                    0xB1 => (tmp ^ tmp.count_ones() as u8).wrapping_sub(hashhog_bytes[cachehog_idx]),                    // ones count bits
                    0xB2 => ((tmp >> 4) ^ data[pos2 as usize] | (tmp & 0x0F)) ^ hashhog_bytes[cachehog_idx], // left nibble XOR with end of data
                    0xB3 => tmp.rotate_right(3).wrapping_sub(hashhog_bytes[cachehog_idx]),                             // rotate right 3
                    0xB4 => (!tmp).wrapping_add(hashhog_bytes[cachehog_idx]),                                            // binary NOT operator
                    0xB5 => ((tmp >> 4) | (tmp & 0x0F).wrapping_mul(tmp)).wrapping_add(hashhog_bytes[cachehog_idx]),     // right nibble *
                    0xB6 => tmp.wrapping_sub(tmp ^ 97).wrapping_sub(hashhog_bytes[cachehog_idx]),                            // XOR and
                    0xB7 => (tmp ^ 0b01010101).wrapping_mul(hashhog_bytes[cachehog_idx]), // invert odd bits
                    0xB8 => ((tmp >> 4) | (tmp & 0x0F).rotate_left(3)).wrapping_mul(hashhog_bytes[cachehog_idx]), // rotate left 3 bits right nibble
                    0xB9 => ((tmp >> 4).rotate_left(3) | (tmp & 0x0F)).wrapping_sub(hashhog_bytes[cachehog_idx]), // rotate left 3 bits left nibble
                    0xBA => tmp.wrapping_mul((tmp.trailing_ones() as u8).wrapping_add(7)) ^ hashhog_bytes[cachehog_idx],
                    0xBB => (((tmp >> 1) & 0b01010101) | ((tmp << 1) & 0b10101010)).wrapping_sub(hashhog_bytes[cachehog_idx]), // swap adjacent bits
                    0xBC => tmp.wrapping_sub(tmp ^ 97) ^ hashhog_bytes[cachehog_idx],                            // XOR and
                    0xBD => ((tmp >> 4) | (tmp & 0x0F).rotate_left(1)).wrapping_mul(hashhog_bytes[cachehog_idx]), // rotate left 1 bits right nibble
                    0xBE => ((tmp >> 4).rotate_right(3) | (tmp & 0x0F)) ^ hashhog_bytes[cachehog_idx], // rotate right 3 bits left nibble
                    0xBF => ((tmp >> 4).wrapping_mul(tmp) | (tmp & 0x0F)).wrapping_sub(hashhog_bytes[cachehog_idx]),     // left nibble *
                    0xC0 => tmp ^ tmp.rotate_left(6).wrapping_sub(hashhog_bytes[cachehog_idx]),                        // rotate left 6, XOR
                    0xC1 => tmp.rotate_left(3) ^ hashhog_bytes[cachehog_idx],                              // rotate left 3
                    0xC2 => tmp ^ tmp.rotate_right(4).wrapping_mul(hashhog_bytes[cachehog_idx]),                       // rotate right 4, XOR
                    0xC3 => ((tmp >> 4).rotate_left(1) | (tmp & 0x0F)).wrapping_add(hashhog_bytes[cachehog_idx]), // rotate left 1 left nibble
                    0xC4 => tmp ^ data[pos2 as usize].wrapping_add(hashhog_bytes[cachehog_idx]), // XOR with end of data
                    0xC5 => tmp.wrapping_mul((tmp.count_zeros() as u8).wrapping_add(1)).wrapping_sub(hashhog_bytes[cachehog_idx]),
                    0xC6 => ((tmp >> 4) | (tmp & 0x0F).wrapping_mul(tmp)) ^ hashhog_bytes[cachehog_idx],     // right nibble *
                    0xC7 => tmp.wrapping_add(tmp.count_ones() as u8) ^ hashhog_bytes[cachehog_idx],
                    0xC8 => ((tmp >> 4) | (tmp & 0x0F).rotate_left(3)) ^ hashhog_bytes[cachehog_idx], // rotate left 3 bits right nibble
                    0xC9 => (!tmp).wrapping_sub(hashhog_bytes[cachehog_idx]),                                            // binary NOT operator
                    0xCA => ((tmp >> 4) | (tmp & 0x0F).reverse_bits()).wrapping_sub(hashhog_bytes[cachehog_idx]), // reverse right nibble
                    0xCB => tmp ^ tmp.rotate_right(6).wrapping_mul(hashhog_bytes[cachehog_idx]),                       // rotate right 6, XOR
                    0xCC => tmp ^ tmp.rotate_left(4) ^ hashhog_bytes[cachehog_idx],                        // rotate left 4, XOR
                    0xCD => ((tmp >> 4).rotate_left(1) | (tmp & 0x0F)).wrapping_mul(hashhog_bytes[cachehog_idx]), // rotate left 1 left nibble
                    0xCE => (tmp ^ 0b10101010).wrapping_sub(hashhog_bytes[cachehog_idx]), // invert even bits
                    0xCF => tmp.wrapping_shl((tmp & 3) as u32).wrapping_add(hashhog_bytes[cachehog_idx]),              // shift left
                    0xD0 => tmp ^ tmp.rotate_right(6) ^ hashhog_bytes[cachehog_idx],                       // rotate right 6, XOR
                    0xD1 => ((tmp >> 4).rotate_right(3) | (tmp & 0x0F)).wrapping_sub(hashhog_bytes[cachehog_idx]), // rotate right 3 bits left nibble
                    0xD2 => tmp.rotate_left(7) ^ hashhog_bytes[cachehog_idx],                              // rotate left 7
                    0xD3 => tmp.rotate_right(3).wrapping_mul(hashhog_bytes[cachehog_idx]),                             // rotate right 3
                    0xD4 => ((tmp >> 4).wrapping_add(tmp) | (tmp & 0x0F)) ^ hashhog_bytes[cachehog_idx],     // left nibble +
                    0xD5 => tmp.wrapping_mul(data[pos1 as usize]).wrapping_add(hashhog_bytes[cachehog_idx]), // * with beginning of data
                    0xD6 => tmp & data[pos1 as usize]  ^ hashhog_bytes[cachehog_idx], // AND with beginning of data
                    0xD7 => ((tmp >> 4) ^ 0b1010 | (tmp & 0x0F)).wrapping_sub(hashhog_bytes[cachehog_idx]), // invert even bits left nibble
                    0xD8 => tmp ^ 0b10101010 ^ hashhog_bytes[cachehog_idx], // invert even bits
                    0xD9 => ((tmp >> 4).rotate_left(1) | (tmp & 0x0F)).wrapping_sub(hashhog_bytes[cachehog_idx]), // rotate left 1 left nibble
                    0xDA => ((tmp >> 4).wrapping_add(tmp) | (tmp & 0x0F)).wrapping_sub(hashhog_bytes[cachehog_idx]),     // left nibble +
                    0xDB => tmp ^ tmp.rotate_left(6) ^ hashhog_bytes[cachehog_idx],                        // rotate left 6, XOR
                    0xDC => tmp.rotate_left(5) ^ hashhog_bytes[cachehog_idx],                              // rotate left 5
                    0xDD => tmp.rotate_left(3).wrapping_mul(hashhog_bytes[cachehog_idx]),                              // rotate left 3
                    0xDE => tmp ^ data[pos1 as usize].wrapping_sub(hashhog_bytes[cachehog_idx]), // XOR with beginning of data
                    0xDF => tmp.wrapping_add(tmp.count_ones() as u8).wrapping_sub(hashhog_bytes[cachehog_idx]),
                    0xE0 => tmp ^ data[pos1 as usize].wrapping_add(hashhog_bytes[cachehog_idx]), // XOR with beginning of data
                    0xE1 => tmp.rotate_right(7).wrapping_sub(hashhog_bytes[cachehog_idx]),                             // rotate right 7
                    0xE2 => ((tmp >> 4) | (tmp & 0x0F).rotate_left(1)) ^ hashhog_bytes[cachehog_idx], // rotate left 1 bits right nibble
                    0xE3 => tmp ^ data[pos2 as usize].wrapping_mul(hashhog_bytes[cachehog_idx]), // XOR with end of data
                    0xE4 => tmp.rotate_right(7) ^ hashhog_bytes[cachehog_idx],                             // rotate right 7
                    0xE5 => (((tmp >> 1) & 0b01010101) | ((tmp << 1) & 0b10101010)).wrapping_add(hashhog_bytes[cachehog_idx]), // swap adjacent bits
                    0xE6 => tmp ^ 0b01010101 ^ hashhog_bytes[cachehog_idx], // invert odd bits
                    0xE7 => ((tmp >> 4) | (tmp & 0x0F) ^ data[pos2 as usize]).wrapping_mul(hashhog_bytes[cachehog_idx]), // right nibble XOR with end of data
                    0xE8 => ((tmp >> 4).rotate_right(1) | (tmp & 0x0F)).wrapping_sub(hashhog_bytes[cachehog_idx]), // rotate right 1 left nibble
                    0xE9 => tmp.reverse_bits() ^ hashhog_bytes[cachehog_idx],                              // reverse bits
                    0xEA => tmp.wrapping_sub((tmp.leading_zeros() as u8).wrapping_mul(43)).wrapping_mul(hashhog_bytes[cachehog_idx]),
                    0xEB => tmp ^ tmp.rotate_right(4).wrapping_sub(hashhog_bytes[cachehog_idx]),                       // rotate right 4, XOR
                    0xEC => tmp.rotate_right(1) ^ hashhog_bytes[cachehog_idx],                             // rotate right 1
                    0xED => tmp ^ data[pos1 as usize]  ^ hashhog_bytes[cachehog_idx], // XOR with beginning of data
                    0xEE => tmp.rotate_left(5).wrapping_add(hashhog_bytes[cachehog_idx]),                              // rotate left 5
                    0xEF => ((tmp >> 4) ^ 0b0101 | (tmp & 0x0F)).wrapping_sub(hashhog_bytes[cachehog_idx]), // invert odd bits left nibble
                    0xF0 => ((tmp >> 4) | (tmp & 0x0F) ^ 0b1010) ^ hashhog_bytes[cachehog_idx], // invert even bits right nibble
                    0xF1 => ((tmp >> 4) | (tmp & 0x0F).reverse_bits()) ^ hashhog_bytes[cachehog_idx], // reverse right nibble
                    0xF2 => tmp.wrapping_sub((tmp.leading_zeros() as u8).wrapping_mul(43)).wrapping_sub(hashhog_bytes[cachehog_idx]),
                    0xF3 => tmp.wrapping_mul((tmp.count_zeros() as u8).wrapping_add(1)).wrapping_mul(hashhog_bytes[cachehog_idx]),
                    0xF4 => tmp.wrapping_add(tmp.count_ones() as u8).wrapping_mul(hashhog_bytes[cachehog_idx]),
                    0xF5 => ((tmp >> 4).wrapping_mul(tmp) | (tmp & 0x0F)).wrapping_add(hashhog_bytes[cachehog_idx]),     // left nibble *
                    0xF6 => tmp.wrapping_shl((tmp & 3) as u32).wrapping_sub(hashhog_bytes[cachehog_idx]),              // shift left
                    0xF7 => ((tmp >> 4) & data[pos2 as usize] | (tmp & 0x0F)) ^ hashhog_bytes[cachehog_idx], // left nibble AND with end of data
                    0xF8 => ((tmp >> 4).rotate_right(tmp as u32) | (tmp & 0x0F)).wrapping_sub(hashhog_bytes[cachehog_idx]), // rotate random left nibble
                    0xF9 => tmp & data[pos2 as usize].wrapping_add(hashhog_bytes[cachehog_idx]), // AND with end of data
                    0xFA => tmp ^ tmp.rotate_left(4).wrapping_sub(hashhog_bytes[cachehog_idx]),                        // rotate left 4, XOR
                    0xFB => ((tmp >> 4).rotate_left(tmp as u32) | (tmp & 0x0F)).wrapping_add(hashhog_bytes[cachehog_idx]), // rotate left random left nibble
                    0xFC => ((tmp >> 4) | (tmp & 0x0F).rotate_right(1)) ^ hashhog_bytes[cachehog_idx], // rotate right 1 bits right nibble
                    0xFD => ((tmp >> 4) | (tmp & 0x0F) & data[pos2 as usize]).wrapping_add(hashhog_bytes[cachehog_idx]), // right nibble AND with end of data
                    0xFE => tmp.wrapping_mul(data[pos1 as usize])  ^ hashhog_bytes[cachehog_idx], // * with beginning of data
                    0xFF => ((tmp >> 4) ^ 0b0101 | (tmp & 0x0F)).wrapping_add(hashhog_bytes[cachehog_idx]), // invert odd bits left nibble
                    _ => unreachable!("Unknown OP reached with OP ID {:x}", op),
                };
                hashhog_bytes[cachehog_idx] = tmp;
            }
            // Push tmp to data
            data[i as usize] = tmp;
            
            if let 512..=767 = branch {
                // More deviations.
                prev_lhash = prev_lhash.wrapping_add(lhash);
                lhash = xxh3_calc(&data[..pos2 as usize], tries);
            }
        }

        let dp1 = data[pos1 as usize];
        let dp2 = data[pos2 as usize];
        let dp_minus = dp1.wrapping_sub(dp2);

        // 6.25 % probability.
        if dp_minus < 0x10 {
            // More deviations.
            prev_lhash = prev_lhash.wrapping_add(lhash);
            lhash = xxh3_calc(&data[..pos2 as usize], tries);
        }

        // 12.5 % probability.
        if dp_minus < 0x20 {
            // More deviations.
            prev_lhash = prev_lhash.wrapping_add(lhash);
            lhash = fnv1a_calc(&data[..pos2 as usize]);
        }

        // 18.75 % probability.
        if dp_minus < 0x30 {
            // More deviations.
            prev_lhash = prev_lhash.wrapping_add(lhash);
            lhash = sip24_calc(&data[..pos2 as usize], tries, prev_lhash);
        }

        // 25% probability.
        if dp_minus <= 0x40 {
            // Do the rc4.
            stream = data.to_vec();
            rc4.apply_keystream(&mut stream);
            data.copy_from_slice(&stream);
        }

        data[255] ^= data[pos1 as usize] ^ data[pos2 as usize];

        // Copy all the tmp states.
        scratch_data[((tries - 1) * 256) as usize..(tries * 256) as usize].copy_from_slice(&data);

        // Keep looping until condition is satisfied.
        if tries > 260 + 16 || (data[255] >= 0xf0 && tries > 260) {
            break;
        }
    }

    // We may discard up to ~ 1KiB data from the stream to ensure that wide number of variants exists.
    let data_len =
        (tries - 4) as u32 * 256 + (((data[253] as u64) << 8 | (data[254] as u64)) as u32 & 0x3ff);

    // Step 7: calculate the final sha256 hash.
    let hash: [u8; 32] = blake3_hash(&scratch_data[..data_len as usize]).into();

    // Return hash.
    Ok(hash)
}

// 0x00 => tmp.wrapping_add(tmp).wrapping_add(hashhog_bytes[cachehog_idx]),                                 // +
// 0x01 => tmp.wrapping_sub(tmp ^ 97).wrapping_add(hashhog_bytes[cachehog_idx]),                            // XOR and
// 0x02 => tmp.wrapping_mul(tmp).wrapping_add(hashhog_bytes[cachehog_idx]),                                 // *
// 0x03 => tmp ^ data[pos2 as usize].wrapping_add(hashhog_bytes[cachehog_idx]), // XOR with end of data
// 0x04 => tmp & data[pos2 as usize].wrapping_add(hashhog_bytes[cachehog_idx]), // AND with end of data
// 0x05 => tmp ^ data[(pos2 as usize + pos1 as usize) / 2].wrapping_add(hashhog_bytes[cachehog_idx]), // AND with midpoint of data
// 0x06 => (!tmp).wrapping_add(hashhog_bytes[cachehog_idx]),                                            // binary NOT operator
// 0x07 => tmp.wrapping_shl((tmp & 3) as u32).wrapping_add(hashhog_bytes[cachehog_idx]),              // shift left
// 0x08 => tmp.wrapping_shr((tmp & 3) as u32).wrapping_add(hashhog_bytes[cachehog_idx]),              // shift right
// 0x09 => tmp.reverse_bits().wrapping_add(hashhog_bytes[cachehog_idx]),                              // reverse bits
// 0x0A => (tmp ^ tmp.count_ones() as u8).wrapping_add(hashhog_bytes[cachehog_idx]),                    // ones count bits
// 0x0B => tmp.rotate_left(tmp as u32).wrapping_add(hashhog_bytes[cachehog_idx]),                     // rotate left random
// 0x0C => tmp.rotate_left(1).wrapping_add(hashhog_bytes[cachehog_idx]),                              // rotate left 1
// 0x0D => tmp.rotate_left(3).wrapping_add(hashhog_bytes[cachehog_idx]),                              // rotate left 3
// 0x0E => tmp.rotate_left(5).wrapping_add(hashhog_bytes[cachehog_idx]),                              // rotate left 5
// 0x0F => tmp.rotate_left(7).wrapping_add(hashhog_bytes[cachehog_idx]),                              // rotate left 7
// 0x10 => tmp.rotate_right(tmp as u32).wrapping_add(hashhog_bytes[cachehog_idx]),                    // rotate right random
// 0x11 => tmp.rotate_right(1).wrapping_add(hashhog_bytes[cachehog_idx]),                             // rotate right 1
// 0x12 => tmp.rotate_right(3).wrapping_add(hashhog_bytes[cachehog_idx]),                             // rotate right 3
// 0x13 => tmp.rotate_right(5).wrapping_add(hashhog_bytes[cachehog_idx]),                             // rotate right 5
// 0x14 => tmp.rotate_right(7).wrapping_add(hashhog_bytes[cachehog_idx]),                             // rotate right 7
// 0x15 => tmp ^ tmp.rotate_left(2).wrapping_add(hashhog_bytes[cachehog_idx]),                        // rotate left 2, XOR
// 0x16 => tmp ^ tmp.rotate_left(4).wrapping_add(hashhog_bytes[cachehog_idx]),                        // rotate left 4, XOR
// 0x17 => tmp ^ tmp.rotate_left(6).wrapping_add(hashhog_bytes[cachehog_idx]),                        // rotate left 6, XOR
// 0x18 => tmp ^ tmp.rotate_right(2).wrapping_add(hashhog_bytes[cachehog_idx]),                       // rotate right 2, XOR
// 0x19 => tmp ^ tmp.rotate_right(4).wrapping_add(hashhog_bytes[cachehog_idx]),                       // rotate right 4, XOR
// 0x1A => tmp ^ tmp.rotate_right(6).wrapping_add(hashhog_bytes[cachehog_idx]),                       // rotate right 6, XOR
// 0x1B => ((tmp >> 4) | (tmp << 4)).wrapping_add(hashhog_bytes[cachehog_idx]),                       // swap nibbles
// 0x1C => (((tmp >> 1) & 0b01010101) | ((tmp << 1) & 0b10101010)).wrapping_add(hashhog_bytes[cachehog_idx]), // swap adjacent bits
// 0x1D => (tmp ^ 0b01010101).wrapping_add(hashhog_bytes[cachehog_idx]), // invert odd bits
// 0x1E => (tmp ^ 0b10101010).wrapping_add(hashhog_bytes[cachehog_idx]), // invert even bits
// 0x1F => ((tmp >> 4).reverse_bits() | (tmp & 0x0F)).wrapping_add(hashhog_bytes[cachehog_idx]), // reverse left nibble
// 0x20 => ((tmp >> 4) | (tmp & 0x0F).reverse_bits()).wrapping_add(hashhog_bytes[cachehog_idx]), // reverse right nibble
// 0x21 => tmp.wrapping_mul((tmp.count_zeros() as u8).wrapping_add(1)).wrapping_add(hashhog_bytes[cachehog_idx]),
// 0x22 => tmp.wrapping_mul((tmp.trailing_ones() as u8).wrapping_add(7)).wrapping_add(hashhog_bytes[cachehog_idx]),
// 0x23 => tmp.wrapping_add(tmp.count_ones() as u8).wrapping_add(hashhog_bytes[cachehog_idx]),
// 0x24 => tmp.wrapping_sub((tmp.leading_zeros() as u8).wrapping_mul(43)).wrapping_add(hashhog_bytes[cachehog_idx]),
// 0x25 => ((tmp >> 4) ^ 0b0101 | (tmp & 0x0F)).wrapping_add(hashhog_bytes[cachehog_idx]), // invert odd bits left nibble
// 0x26 => ((tmp >> 4) | (tmp & 0x0F) ^ 0b0101).wrapping_add(hashhog_bytes[cachehog_idx]), // invert odd bits right nibble
// 0x27 => ((tmp >> 4) ^ 0b1010 | (tmp & 0x0F)).wrapping_add(hashhog_bytes[cachehog_idx]), // invert even bits left nibble
// 0x28 => ((tmp >> 4) | (tmp & 0x0F) ^ 0b1010).wrapping_add(hashhog_bytes[cachehog_idx]), // invert even bits right nibble
// 0x29 => ((tmp >> 4).rotate_left(1) | (tmp & 0x0F)).wrapping_add(hashhog_bytes[cachehog_idx]), // rotate left 1 left nibble
// 0x2A => ((tmp >> 4) | (tmp & 0x0F).rotate_left(1)).wrapping_add(hashhog_bytes[cachehog_idx]), // rotate left 1 bits right nibble
// 0x2B => ((tmp >> 4).rotate_left(3) | (tmp & 0x0F)).wrapping_add(hashhog_bytes[cachehog_idx]), // rotate left 3 bits left nibble
// 0x2C => ((tmp >> 4) | (tmp & 0x0F).rotate_left(3)).wrapping_add(hashhog_bytes[cachehog_idx]), // rotate left 3 bits right nibble
// 0x2D => ((tmp >> 4).rotate_right(1) | (tmp & 0x0F)).wrapping_add(hashhog_bytes[cachehog_idx]), // rotate right 1 left nibble
// 0x2E => ((tmp >> 4) | (tmp & 0x0F).rotate_right(1)).wrapping_add(hashhog_bytes[cachehog_idx]), // rotate right 1 bits right nibble
// 0x2F => ((tmp >> 4).rotate_right(3) | (tmp & 0x0F)).wrapping_add(hashhog_bytes[cachehog_idx]), // rotate right 3 bits left nibble
// 0x30 => ((tmp >> 4) | (tmp & 0x0F).rotate_right(3)).wrapping_add(hashhog_bytes[cachehog_idx]), // rotate right 3 bits right nibble
// 0x31 => ((tmp >> 4).rotate_left(tmp as u32) | (tmp & 0x0F)).wrapping_add(hashhog_bytes[cachehog_idx]), // rotate left random left nibble
// 0x32 => ((tmp >> 4) | (tmp & 0x0F).rotate_left(tmp as u32)).wrapping_add(hashhog_bytes[cachehog_idx]), // rotate left random right nibble
// 0x33 => ((tmp >> 4).rotate_right(tmp as u32) | (tmp & 0x0F)).wrapping_add(hashhog_bytes[cachehog_idx]), // rotate random left nibble
// 0x34 => ((tmp >> 4) | (tmp & 0x0F).rotate_right(tmp as u32)).wrapping_add(hashhog_bytes[cachehog_idx]), // rotate random bits right nibble
// 0x35 => ((tmp >> 4) ^ data[pos2 as usize] | (tmp & 0x0F)).wrapping_add(hashhog_bytes[cachehog_idx]), // left nibble XOR with end of data
// 0x36 => ((tmp >> 4) | (tmp & 0x0F) ^ data[pos2 as usize]).wrapping_add(hashhog_bytes[cachehog_idx]), // right nibble XOR with end of data
// 0x37 => ((tmp >> 4) & data[pos2 as usize] | (tmp & 0x0F)).wrapping_add(hashhog_bytes[cachehog_idx]), // left nibble AND with end of data
// 0x38 => ((tmp >> 4) | (tmp & 0x0F) & data[pos2 as usize]).wrapping_add(hashhog_bytes[cachehog_idx]), // right nibble AND with end of data
// 0x39 => ((tmp >> 4).wrapping_add(tmp) | (tmp & 0x0F)).wrapping_add(hashhog_bytes[cachehog_idx]),     // left nibble +
// 0x3A => ((tmp >> 4) | (tmp & 0x0F).wrapping_add(tmp)).wrapping_add(hashhog_bytes[cachehog_idx]),     // right nibble +
// 0x3B => ((tmp >> 4).wrapping_mul(tmp) | (tmp & 0x0F)).wrapping_add(hashhog_bytes[cachehog_idx]),     // left nibble *
// 0x3C => ((tmp >> 4) | (tmp & 0x0F).wrapping_mul(tmp)).wrapping_add(hashhog_bytes[cachehog_idx]),     // right nibble *
// 0x3D => tmp ^ data[pos1 as usize].wrapping_add(hashhog_bytes[cachehog_idx]), // XOR with beginning of data
// 0x3E => tmp & data[pos1 as usize].wrapping_add(hashhog_bytes[cachehog_idx]), // AND with beginning of data
// 0x3F => tmp.wrapping_mul(data[pos1 as usize]).wrapping_add(hashhog_bytes[cachehog_idx]), // * with beginning of data
// 0x40 => tmp.wrapping_add(tmp).wrapping_sub(hashhog_bytes[cachehog_idx]),                                 // +
// 0x41 => tmp.wrapping_sub(tmp ^ 97).wrapping_sub(hashhog_bytes[cachehog_idx]),                            // XOR and
// 0x42 => tmp.wrapping_mul(tmp).wrapping_sub(hashhog_bytes[cachehog_idx]),                                 // *
// 0x43 => tmp ^ data[pos2 as usize].wrapping_sub(hashhog_bytes[cachehog_idx]), // XOR with end of data
// 0x44 => tmp & data[pos2 as usize].wrapping_sub(hashhog_bytes[cachehog_idx]), // AND with end of data
// 0x45 => tmp ^ data[(pos2 as usize + pos1 as usize) / 2].wrapping_sub(hashhog_bytes[cachehog_idx]), // AND with midpoint of data
// 0x46 => (!tmp).wrapping_sub(hashhog_bytes[cachehog_idx]),                                            // binary NOT operator
// 0x47 => tmp.wrapping_shl((tmp & 3) as u32).wrapping_sub(hashhog_bytes[cachehog_idx]),              // shift left
// 0x48 => tmp.wrapping_shr((tmp & 3) as u32).wrapping_sub(hashhog_bytes[cachehog_idx]),              // shift right
// 0x49 => tmp.reverse_bits().wrapping_sub(hashhog_bytes[cachehog_idx]),                              // reverse bits
// 0x4A => (tmp ^ tmp.count_ones() as u8).wrapping_sub(hashhog_bytes[cachehog_idx]),                    // ones count bits
// 0x4B => tmp.rotate_left(tmp as u32).wrapping_sub(hashhog_bytes[cachehog_idx]),                     // rotate left random
// 0x4C => tmp.rotate_left(1).wrapping_sub(hashhog_bytes[cachehog_idx]),                              // rotate left 1
// 0x4D => tmp.rotate_left(3).wrapping_sub(hashhog_bytes[cachehog_idx]),                              // rotate left 3
// 0x4E => tmp.rotate_left(5).wrapping_sub(hashhog_bytes[cachehog_idx]),                              // rotate left 5
// 0x4F => tmp.rotate_left(7).wrapping_sub(hashhog_bytes[cachehog_idx]),                              // rotate left 7
// 0x50 => tmp.rotate_right(tmp as u32).wrapping_sub(hashhog_bytes[cachehog_idx]),                    // rotate right random
// 0x51 => tmp.rotate_right(1).wrapping_sub(hashhog_bytes[cachehog_idx]),                             // rotate right 1
// 0x52 => tmp.rotate_right(3).wrapping_sub(hashhog_bytes[cachehog_idx]),                             // rotate right 3
// 0x53 => tmp.rotate_right(5).wrapping_sub(hashhog_bytes[cachehog_idx]),                             // rotate right 5
// 0x54 => tmp.rotate_right(7).wrapping_sub(hashhog_bytes[cachehog_idx]),                             // rotate right 7
// 0x55 => tmp ^ tmp.rotate_left(2).wrapping_sub(hashhog_bytes[cachehog_idx]),                        // rotate left 2, XOR
// 0x56 => tmp ^ tmp.rotate_left(4).wrapping_sub(hashhog_bytes[cachehog_idx]),                        // rotate left 4, XOR
// 0x57 => tmp ^ tmp.rotate_left(6).wrapping_sub(hashhog_bytes[cachehog_idx]),                        // rotate left 6, XOR
// 0x58 => tmp ^ tmp.rotate_right(2).wrapping_sub(hashhog_bytes[cachehog_idx]),                       // rotate right 2, XOR
// 0x59 => tmp ^ tmp.rotate_right(4).wrapping_sub(hashhog_bytes[cachehog_idx]),                       // rotate right 4, XOR
// 0x5A => tmp ^ tmp.rotate_right(6).wrapping_sub(hashhog_bytes[cachehog_idx]),                       // rotate right 6, XOR
// 0x5B => ((tmp >> 4) | (tmp << 4)).wrapping_sub(hashhog_bytes[cachehog_idx]),                       // swap nibbles
// 0x5C => (((tmp >> 1) & 0b01010101) | ((tmp << 1) & 0b10101010)).wrapping_sub(hashhog_bytes[cachehog_idx]), // swap adjacent bits
// 0x5D => (tmp ^ 0b01010101).wrapping_sub(hashhog_bytes[cachehog_idx]), // invert odd bits
// 0x5E => (tmp ^ 0b10101010).wrapping_sub(hashhog_bytes[cachehog_idx]), // invert even bits
// 0x5F => ((tmp >> 4).reverse_bits() | (tmp & 0x0F)).wrapping_sub(hashhog_bytes[cachehog_idx]), // reverse left nibble
// 0x60 => ((tmp >> 4) | (tmp & 0x0F).reverse_bits()).wrapping_sub(hashhog_bytes[cachehog_idx]), // reverse right nibble
// 0x61 => tmp.wrapping_mul((tmp.count_zeros() as u8).wrapping_add(1)).wrapping_sub(hashhog_bytes[cachehog_idx]),
// 0x62 => tmp.wrapping_mul((tmp.trailing_ones() as u8).wrapping_add(7)).wrapping_sub(hashhog_bytes[cachehog_idx]),
// 0x63 => tmp.wrapping_add(tmp.count_ones() as u8).wrapping_sub(hashhog_bytes[cachehog_idx]),
// 0x64 => tmp.wrapping_sub((tmp.leading_zeros() as u8).wrapping_mul(43)).wrapping_sub(hashhog_bytes[cachehog_idx]),
// 0x65 => ((tmp >> 4) ^ 0b0101 | (tmp & 0x0F)).wrapping_sub(hashhog_bytes[cachehog_idx]), // invert odd bits left nibble
// 0x66 => ((tmp >> 4) | (tmp & 0x0F) ^ 0b0101).wrapping_sub(hashhog_bytes[cachehog_idx]), // invert odd bits right nibble
// 0x67 => ((tmp >> 4) ^ 0b1010 | (tmp & 0x0F)).wrapping_sub(hashhog_bytes[cachehog_idx]), // invert even bits left nibble
// 0x68 => ((tmp >> 4) | (tmp & 0x0F) ^ 0b1010).wrapping_sub(hashhog_bytes[cachehog_idx]), // invert even bits right nibble
// 0x69 => ((tmp >> 4).rotate_left(1) | (tmp & 0x0F)).wrapping_sub(hashhog_bytes[cachehog_idx]), // rotate left 1 left nibble
// 0x6A => ((tmp >> 4) | (tmp & 0x0F).rotate_left(1)).wrapping_sub(hashhog_bytes[cachehog_idx]), // rotate left 1 bits right nibble
// 0x6B => ((tmp >> 4).rotate_left(3) | (tmp & 0x0F)).wrapping_sub(hashhog_bytes[cachehog_idx]), // rotate left 3 bits left nibble
// 0x6C => ((tmp >> 4) | (tmp & 0x0F).rotate_left(3)).wrapping_sub(hashhog_bytes[cachehog_idx]), // rotate left 3 bits right nibble
// 0x6D => ((tmp >> 4).rotate_right(1) | (tmp & 0x0F)).wrapping_sub(hashhog_bytes[cachehog_idx]), // rotate right 1 left nibble
// 0x6E => ((tmp >> 4) | (tmp & 0x0F).rotate_right(1)).wrapping_sub(hashhog_bytes[cachehog_idx]), // rotate right 1 bits right nibble
// 0x6F => ((tmp >> 4).rotate_right(3) | (tmp & 0x0F)).wrapping_sub(hashhog_bytes[cachehog_idx]), // rotate right 3 bits left nibble
// 0x70 => ((tmp >> 4) | (tmp & 0x0F).rotate_right(3)).wrapping_sub(hashhog_bytes[cachehog_idx]), // rotate right 3 bits right nibble
// 0x71 => ((tmp >> 4).rotate_left(tmp as u32) | (tmp & 0x0F)).wrapping_sub(hashhog_bytes[cachehog_idx]), // rotate left random left nibble
// 0x72 => ((tmp >> 4) | (tmp & 0x0F).rotate_left(tmp as u32)).wrapping_sub(hashhog_bytes[cachehog_idx]), // rotate left random right nibble
// 0x73 => ((tmp >> 4).rotate_right(tmp as u32) | (tmp & 0x0F)).wrapping_sub(hashhog_bytes[cachehog_idx]), // rotate random left nibble
// 0x74 => ((tmp >> 4) | (tmp & 0x0F).rotate_right(tmp as u32)).wrapping_sub(hashhog_bytes[cachehog_idx]), // rotate random bits right nibble
// 0x75 => ((tmp >> 4) ^ data[pos2 as usize] | (tmp & 0x0F)).wrapping_sub(hashhog_bytes[cachehog_idx]), // left nibble XOR with end of data
// 0x76 => ((tmp >> 4) | (tmp & 0x0F) ^ data[pos2 as usize]).wrapping_sub(hashhog_bytes[cachehog_idx]), // right nibble XOR with end of data
// 0x77 => ((tmp >> 4) & data[pos2 as usize] | (tmp & 0x0F)).wrapping_sub(hashhog_bytes[cachehog_idx]), // left nibble AND with end of data
// 0x78 => ((tmp >> 4) | (tmp & 0x0F) & data[pos2 as usize]).wrapping_sub(hashhog_bytes[cachehog_idx]), // right nibble AND with end of data
// 0x79 => ((tmp >> 4).wrapping_add(tmp) | (tmp & 0x0F)).wrapping_sub(hashhog_bytes[cachehog_idx]),     // left nibble +
// 0x7A => ((tmp >> 4) | (tmp & 0x0F).wrapping_add(tmp)).wrapping_sub(hashhog_bytes[cachehog_idx]),     // right nibble +
// 0x7B => ((tmp >> 4).wrapping_mul(tmp) | (tmp & 0x0F)).wrapping_sub(hashhog_bytes[cachehog_idx]),     // left nibble *
// 0x7C => ((tmp >> 4) | (tmp & 0x0F).wrapping_mul(tmp)).wrapping_sub(hashhog_bytes[cachehog_idx]),     // right nibble *
// 0x7D => tmp ^ data[pos1 as usize].wrapping_sub(hashhog_bytes[cachehog_idx]), // XOR with beginning of data
// 0x7E => tmp & data[pos1 as usize].wrapping_sub(hashhog_bytes[cachehog_idx]), // AND with beginning of data
// 0x7F => tmp.wrapping_mul(data[pos1 as usize]).wrapping_sub(hashhog_bytes[cachehog_idx]), // * with beginning of data
// 0x80 => tmp.wrapping_add(tmp).wrapping_mul(hashhog_bytes[cachehog_idx]),                                 // +
// 0x81 => tmp.wrapping_sub(tmp ^ 97).wrapping_mul(hashhog_bytes[cachehog_idx]),                            // XOR and
// 0x82 => tmp.wrapping_mul(tmp).wrapping_mul(hashhog_bytes[cachehog_idx]),                                 // *
// 0x83 => tmp ^ data[pos2 as usize].wrapping_mul(hashhog_bytes[cachehog_idx]), // XOR with end of data
// 0x84 => tmp & data[pos2 as usize].wrapping_mul(hashhog_bytes[cachehog_idx]), // AND with end of data
// 0x85 => tmp ^ data[(pos2 as usize + pos1 as usize) / 2].wrapping_mul(hashhog_bytes[cachehog_idx]), // AND with midpoint of data
// 0x86 => (!tmp).wrapping_mul(hashhog_bytes[cachehog_idx]),                                            // binary NOT operator
// 0x87 => tmp.wrapping_shl((tmp & 3) as u32).wrapping_mul(hashhog_bytes[cachehog_idx]),              // shift left
// 0x88 => tmp.wrapping_shr((tmp & 3) as u32).wrapping_mul(hashhog_bytes[cachehog_idx]),              // shift right
// 0x89 => tmp.reverse_bits().wrapping_mul(hashhog_bytes[cachehog_idx]),                              // reverse bits
// 0x8A => (tmp ^ tmp.count_ones() as u8).wrapping_mul(hashhog_bytes[cachehog_idx]),                    // ones count bits
// 0x8B => tmp.rotate_left(tmp as u32).wrapping_mul(hashhog_bytes[cachehog_idx]),                     // rotate left random
// 0x8C => tmp.rotate_left(1).wrapping_mul(hashhog_bytes[cachehog_idx]),                              // rotate left 1
// 0x8D => tmp.rotate_left(3).wrapping_mul(hashhog_bytes[cachehog_idx]),                              // rotate left 3
// 0x8E => tmp.rotate_left(5).wrapping_mul(hashhog_bytes[cachehog_idx]),                              // rotate left 5
// 0x8F => tmp.rotate_left(7).wrapping_mul(hashhog_bytes[cachehog_idx]),                              // rotate left 7
// 0x90 => tmp.rotate_right(tmp as u32).wrapping_mul(hashhog_bytes[cachehog_idx]),                    // rotate right random
// 0x91 => tmp.rotate_right(1).wrapping_mul(hashhog_bytes[cachehog_idx]),                             // rotate right 1
// 0x92 => tmp.rotate_right(3).wrapping_mul(hashhog_bytes[cachehog_idx]),                             // rotate right 3
// 0x93 => tmp.rotate_right(5).wrapping_mul(hashhog_bytes[cachehog_idx]),                             // rotate right 5
// 0x94 => tmp.rotate_right(7).wrapping_mul(hashhog_bytes[cachehog_idx]),                             // rotate right 7
// 0x95 => tmp ^ tmp.rotate_left(2).wrapping_mul(hashhog_bytes[cachehog_idx]),                        // rotate left 2, XOR
// 0x96 => tmp ^ tmp.rotate_left(4).wrapping_mul(hashhog_bytes[cachehog_idx]),                        // rotate left 4, XOR
// 0x97 => tmp ^ tmp.rotate_left(6).wrapping_mul(hashhog_bytes[cachehog_idx]),                        // rotate left 6, XOR
// 0x98 => tmp ^ tmp.rotate_right(2).wrapping_mul(hashhog_bytes[cachehog_idx]),                       // rotate right 2, XOR
// 0x99 => tmp ^ tmp.rotate_right(4).wrapping_mul(hashhog_bytes[cachehog_idx]),                       // rotate right 4, XOR
// 0x9A => tmp ^ tmp.rotate_right(6).wrapping_mul(hashhog_bytes[cachehog_idx]),                       // rotate right 6, XOR
// 0x9B => ((tmp >> 4) | (tmp << 4)).wrapping_mul(hashhog_bytes[cachehog_idx]),                       // swap nibbles
// 0x9C => (((tmp >> 1) & 0b01010101) | ((tmp << 1) & 0b10101010)).wrapping_mul(hashhog_bytes[cachehog_idx]), // swap adjacent bits
// 0x9D => (tmp ^ 0b01010101).wrapping_mul(hashhog_bytes[cachehog_idx]), // invert odd bits
// 0x9E => (tmp ^ 0b10101010).wrapping_mul(hashhog_bytes[cachehog_idx]), // invert even bits
// 0x9F => ((tmp >> 4).reverse_bits() | (tmp & 0x0F)).wrapping_mul(hashhog_bytes[cachehog_idx]), // reverse left nibble
// 0xA0 => ((tmp >> 4) | (tmp & 0x0F).reverse_bits()).wrapping_mul(hashhog_bytes[cachehog_idx]), // reverse right nibble
// 0xA1 => tmp.wrapping_mul((tmp.count_zeros() as u8).wrapping_add(1)).wrapping_mul(hashhog_bytes[cachehog_idx]),
// 0xA2 => tmp.wrapping_mul((tmp.trailing_ones() as u8).wrapping_add(7)).wrapping_mul(hashhog_bytes[cachehog_idx]),
// 0xA3 => tmp.wrapping_add(tmp.count_ones() as u8).wrapping_mul(hashhog_bytes[cachehog_idx]),
// 0xA4 => tmp.wrapping_sub((tmp.leading_zeros() as u8).wrapping_mul(43)).wrapping_mul(hashhog_bytes[cachehog_idx]),
// 0xA5 => ((tmp >> 4) ^ 0b0101 | (tmp & 0x0F)).wrapping_mul(hashhog_bytes[cachehog_idx]), // invert odd bits left nibble
// 0xA6 => ((tmp >> 4) | (tmp & 0x0F) ^ 0b0101).wrapping_mul(hashhog_bytes[cachehog_idx]), // invert odd bits right nibble
// 0xA7 => ((tmp >> 4) ^ 0b1010 | (tmp & 0x0F)).wrapping_mul(hashhog_bytes[cachehog_idx]), // invert even bits left nibble
// 0xA8 => ((tmp >> 4) | (tmp & 0x0F) ^ 0b1010).wrapping_mul(hashhog_bytes[cachehog_idx]), // invert even bits right nibble
// 0xA9 => ((tmp >> 4).rotate_left(1) | (tmp & 0x0F)).wrapping_mul(hashhog_bytes[cachehog_idx]), // rotate left 1 left nibble
// 0xAA => ((tmp >> 4) | (tmp & 0x0F).rotate_left(1)).wrapping_mul(hashhog_bytes[cachehog_idx]), // rotate left 1 bits right nibble
// 0xAB => ((tmp >> 4).rotate_left(3) | (tmp & 0x0F)).wrapping_mul(hashhog_bytes[cachehog_idx]), // rotate left 3 bits left nibble
// 0xAC => ((tmp >> 4) | (tmp & 0x0F).rotate_left(3)).wrapping_mul(hashhog_bytes[cachehog_idx]), // rotate left 3 bits right nibble
// 0xAD => ((tmp >> 4).rotate_right(1) | (tmp & 0x0F)).wrapping_mul(hashhog_bytes[cachehog_idx]), // rotate right 1 left nibble
// 0xAE => ((tmp >> 4) | (tmp & 0x0F).rotate_right(1)).wrapping_mul(hashhog_bytes[cachehog_idx]), // rotate right 1 bits right nibble
// 0xAF => ((tmp >> 4).rotate_right(3) | (tmp & 0x0F)).wrapping_mul(hashhog_bytes[cachehog_idx]), // rotate right 3 bits left nibble
// 0xB0 => ((tmp >> 4) | (tmp & 0x0F).rotate_right(3)).wrapping_mul(hashhog_bytes[cachehog_idx]), // rotate right 3 bits right nibble
// 0xB1 => ((tmp >> 4).rotate_left(tmp as u32) | (tmp & 0x0F)).wrapping_mul(hashhog_bytes[cachehog_idx]), // rotate left random left nibble
// 0xB2 => ((tmp >> 4) | (tmp & 0x0F).rotate_left(tmp as u32)).wrapping_mul(hashhog_bytes[cachehog_idx]), // rotate left random right nibble
// 0xB3 => ((tmp >> 4).rotate_right(tmp as u32) | (tmp & 0x0F)).wrapping_mul(hashhog_bytes[cachehog_idx]), // rotate random left nibble
// 0xB4 => ((tmp >> 4) | (tmp & 0x0F).rotate_right(tmp as u32)).wrapping_mul(hashhog_bytes[cachehog_idx]), // rotate random bits right nibble
// 0xB5 => ((tmp >> 4) ^ data[pos2 as usize] | (tmp & 0x0F)).wrapping_mul(hashhog_bytes[cachehog_idx]), // left nibble XOR with end of data
// 0xB6 => ((tmp >> 4) | (tmp & 0x0F) ^ data[pos2 as usize]).wrapping_mul(hashhog_bytes[cachehog_idx]), // right nibble XOR with end of data
// 0xB7 => ((tmp >> 4) & data[pos2 as usize] | (tmp & 0x0F)).wrapping_mul(hashhog_bytes[cachehog_idx]), // left nibble AND with end of data
// 0xB8 => ((tmp >> 4) | (tmp & 0x0F) & data[pos2 as usize]).wrapping_mul(hashhog_bytes[cachehog_idx]), // right nibble AND with end of data
// 0xB9 => ((tmp >> 4).wrapping_add(tmp) | (tmp & 0x0F)).wrapping_mul(hashhog_bytes[cachehog_idx]),     // left nibble +
// 0xBA => ((tmp >> 4) | (tmp & 0x0F).wrapping_add(tmp)).wrapping_mul(hashhog_bytes[cachehog_idx]),     // right nibble +
// 0xBB => ((tmp >> 4).wrapping_mul(tmp) | (tmp & 0x0F)).wrapping_mul(hashhog_bytes[cachehog_idx]),     // left nibble *
// 0xBC => ((tmp >> 4) | (tmp & 0x0F).wrapping_mul(tmp)).wrapping_mul(hashhog_bytes[cachehog_idx]),     // right nibble *
// 0xBD => tmp ^ data[pos1 as usize].wrapping_mul(hashhog_bytes[cachehog_idx]), // XOR with beginning of data
// 0xBE => tmp & data[pos1 as usize].wrapping_mul(hashhog_bytes[cachehog_idx]), // AND with beginning of data
// 0xBF => tmp.wrapping_mul(data[pos1 as usize]).wrapping_mul(hashhog_bytes[cachehog_idx]), // * with beginning of data
// 0xC0 => tmp.wrapping_add(tmp) ^ hashhog_bytes[cachehog_idx],                                 // +
// 0xC1 => tmp.wrapping_sub(tmp ^ 97) ^ hashhog_bytes[cachehog_idx],                            // XOR and
// 0xC2 => tmp.wrapping_mul(tmp) ^ hashhog_bytes[cachehog_idx],                                 // *
// 0xC3 => tmp ^ data[pos2 as usize] ^ hashhog_bytes[cachehog_idx], // XOR with end of data
// 0xC4 => tmp & data[pos2 as usize] ^ hashhog_bytes[cachehog_idx], // AND with end of data
// 0xC5 => tmp ^ data[(pos2 as usize + pos1 as usize) / 2] ^ hashhog_bytes[cachehog_idx], // AND with midpoint of data
// 0xC6 => !tmp ^ hashhog_bytes[cachehog_idx],                                            // binary NOT operator
// 0xC7 => tmp.wrapping_shl((tmp & 3) as u32) ^ hashhog_bytes[cachehog_idx],              // shift left
// 0xC8 => tmp.wrapping_shr((tmp & 3) as u32) ^ hashhog_bytes[cachehog_idx],              // shift right
// 0xC9 => tmp.reverse_bits() ^ hashhog_bytes[cachehog_idx],                              // reverse bits
// 0xCA => tmp ^ tmp.count_ones() as u8 ^ hashhog_bytes[cachehog_idx],                    // ones count bits
// 0xCB => tmp.rotate_left(tmp as u32) ^ hashhog_bytes[cachehog_idx],                     // rotate left random
// 0xCC => tmp.rotate_left(1) ^ hashhog_bytes[cachehog_idx],                              // rotate left 1
// 0xCD => tmp.rotate_left(3) ^ hashhog_bytes[cachehog_idx],                              // rotate left 3
// 0xCE => tmp.rotate_left(5) ^ hashhog_bytes[cachehog_idx],                              // rotate left 5
// 0xCF => tmp.rotate_left(7) ^ hashhog_bytes[cachehog_idx],                              // rotate left 7
// 0xD0 => tmp.rotate_right(tmp as u32) ^ hashhog_bytes[cachehog_idx],                    // rotate right random
// 0xD1 => tmp.rotate_right(1) ^ hashhog_bytes[cachehog_idx],                             // rotate right 1
// 0xD2 => tmp.rotate_right(3) ^ hashhog_bytes[cachehog_idx],                             // rotate right 3
// 0xD3 => tmp.rotate_right(5) ^ hashhog_bytes[cachehog_idx],                             // rotate right 5
// 0xD4 => tmp.rotate_right(7) ^ hashhog_bytes[cachehog_idx],                             // rotate right 7
// 0xD5 => tmp ^ tmp.rotate_left(2) ^ hashhog_bytes[cachehog_idx],                        // rotate left 2, XOR
// 0xD6 => tmp ^ tmp.rotate_left(4) ^ hashhog_bytes[cachehog_idx],                        // rotate left 4, XOR
// 0xD7 => tmp ^ tmp.rotate_left(6) ^ hashhog_bytes[cachehog_idx],                        // rotate left 6, XOR
// 0xD8 => tmp ^ tmp.rotate_right(2) ^ hashhog_bytes[cachehog_idx],                       // rotate right 2, XOR
// 0xD9 => tmp ^ tmp.rotate_right(4) ^ hashhog_bytes[cachehog_idx],                       // rotate right 4, XOR
// 0xDA => tmp ^ tmp.rotate_right(6) ^ hashhog_bytes[cachehog_idx],                       // rotate right 6, XOR
// 0xDB => ((tmp >> 4) | (tmp << 4)) ^ hashhog_bytes[cachehog_idx],                       // swap nibbles
// 0xDC => (((tmp >> 1) & 0b01010101) | ((tmp << 1) & 0b10101010)) ^ hashhog_bytes[cachehog_idx], // swap adjacent bits
// 0xDD => tmp ^ 0b01010101 ^ hashhog_bytes[cachehog_idx], // invert odd bits
// 0xDE => tmp ^ 0b10101010 ^ hashhog_bytes[cachehog_idx], // invert even bits
// 0xDF => ((tmp >> 4).reverse_bits() | (tmp & 0x0F)) ^ hashhog_bytes[cachehog_idx], // reverse left nibble
// 0xE0 => ((tmp >> 4) | (tmp & 0x0F).reverse_bits()) ^ hashhog_bytes[cachehog_idx], // reverse right nibble
// 0xE1 => tmp.wrapping_mul((tmp.count_zeros() as u8).wrapping_add(1)) ^ hashhog_bytes[cachehog_idx],
// 0xE2 => tmp.wrapping_mul((tmp.trailing_ones() as u8).wrapping_add(7)) ^ hashhog_bytes[cachehog_idx],
// 0xE3 => tmp.wrapping_add(tmp.count_ones() as u8) ^ hashhog_bytes[cachehog_idx],
// 0xE4 => tmp.wrapping_sub((tmp.leading_zeros() as u8).wrapping_mul(43)) ^ hashhog_bytes[cachehog_idx],
// 0xE5 => ((tmp >> 4) ^ 0b0101 | (tmp & 0x0F)) ^ hashhog_bytes[cachehog_idx], // invert odd bits left nibble
// 0xE6 => ((tmp >> 4) | (tmp & 0x0F) ^ 0b0101) ^ hashhog_bytes[cachehog_idx], // invert odd bits right nibble
// 0xE7 => ((tmp >> 4) ^ 0b1010 | (tmp & 0x0F)) ^ hashhog_bytes[cachehog_idx], // invert even bits left nibble
// 0xE8 => ((tmp >> 4) | (tmp & 0x0F) ^ 0b1010) ^ hashhog_bytes[cachehog_idx], // invert even bits right nibble
// 0xE9 => ((tmp >> 4).rotate_left(1) | (tmp & 0x0F)) ^ hashhog_bytes[cachehog_idx], // rotate left 1 left nibble
// 0xEA => ((tmp >> 4) | (tmp & 0x0F).rotate_left(1)) ^ hashhog_bytes[cachehog_idx], // rotate left 1 bits right nibble
// 0xEB => ((tmp >> 4).rotate_left(3) | (tmp & 0x0F)) ^ hashhog_bytes[cachehog_idx], // rotate left 3 bits left nibble
// 0xEC => ((tmp >> 4) | (tmp & 0x0F).rotate_left(3)) ^ hashhog_bytes[cachehog_idx], // rotate left 3 bits right nibble
// 0xED => ((tmp >> 4).rotate_right(1) | (tmp & 0x0F)) ^ hashhog_bytes[cachehog_idx], // rotate right 1 left nibble
// 0xEE => ((tmp >> 4) | (tmp & 0x0F).rotate_right(1)) ^ hashhog_bytes[cachehog_idx], // rotate right 1 bits right nibble
// 0xEF => ((tmp >> 4).rotate_right(3) | (tmp & 0x0F)) ^ hashhog_bytes[cachehog_idx], // rotate right 3 bits left nibble
// 0xF0 => ((tmp >> 4) | (tmp & 0x0F).rotate_right(3)) ^ hashhog_bytes[cachehog_idx], // rotate right 3 bits right nibble
// 0xF1 => ((tmp >> 4).rotate_left(tmp as u32) | (tmp & 0x0F)) ^ hashhog_bytes[cachehog_idx], // rotate left random left nibble
// 0xF2 => ((tmp >> 4) | (tmp & 0x0F).rotate_left(tmp as u32)) ^ hashhog_bytes[cachehog_idx], // rotate left random right nibble
// 0xF3 => ((tmp >> 4).rotate_right(tmp as u32) | (tmp & 0x0F)) ^ hashhog_bytes[cachehog_idx], // rotate random left nibble
// 0xF4 => ((tmp >> 4) | (tmp & 0x0F).rotate_right(tmp as u32)) ^ hashhog_bytes[cachehog_idx], // rotate random bits right nibble
// 0xF5 => ((tmp >> 4) ^ data[pos2 as usize] | (tmp & 0x0F)) ^ hashhog_bytes[cachehog_idx], // left nibble XOR with end of data
// 0xF6 => ((tmp >> 4) | (tmp & 0x0F) ^ data[pos2 as usize]) ^ hashhog_bytes[cachehog_idx], // right nibble XOR with end of data
// 0xF7 => ((tmp >> 4) & data[pos2 as usize] | (tmp & 0x0F)) ^ hashhog_bytes[cachehog_idx], // left nibble AND with end of data
// 0xF8 => ((tmp >> 4) | (tmp & 0x0F) & data[pos2 as usize]) ^ hashhog_bytes[cachehog_idx], // right nibble AND with end of data
// 0xF9 => ((tmp >> 4).wrapping_add(tmp) | (tmp & 0x0F)) ^ hashhog_bytes[cachehog_idx],     // left nibble +
// 0xFA => ((tmp >> 4) | (tmp & 0x0F).wrapping_add(tmp)) ^ hashhog_bytes[cachehog_idx],     // right nibble +
// 0xFB => ((tmp >> 4).wrapping_mul(tmp) | (tmp & 0x0F)) ^ hashhog_bytes[cachehog_idx],     // left nibble *
// 0xFC => ((tmp >> 4) | (tmp & 0x0F).wrapping_mul(tmp)) ^ hashhog_bytes[cachehog_idx],     // right nibble *
// 0xFD => tmp ^ data[pos1 as usize]  ^ hashhog_bytes[cachehog_idx], // XOR with beginning of data
// 0xFE => tmp & data[pos1 as usize]  ^ hashhog_bytes[cachehog_idx], // AND with beginning of data
// 0xFF => tmp.wrapping_mul(data[pos1 as usize])  ^ hashhog_bytes[cachehog_idx], // * with beginning of data