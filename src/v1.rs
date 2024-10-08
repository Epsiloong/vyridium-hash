// Public crates.
use chacha20::{cipher::KeyIvInit, ChaCha20};
use rc4::{Rc4, KeyInit, StreamCipher};
use sha2::{Sha512, Digest};
use blake3::hash as blake3_hash;
use siphasher::sip::SipHasher24;
use std::hash::Hasher;

use crate::{Error, Hash};

// This is the maximum of the scratchpad.
const MAX_LENGTH: u32 = (256 * 384) - 1;
// Number of unique operations
const OP_COUNT: u64 = 64;
// Number of operations per branch
const OP_PER_BRANCH: u64 = 8;

// Generate cachehog
fn populate_cachehog(seed: &[u8], len: usize) -> Vec<u8> {
    let mut cachehog = vec![0u8; len];
    let mut hasher = Sha512::new();
    hasher.update(seed);

    for i in 0..len {
        let hash = hasher.finalize_reset();
        cachehog[i] = hash[0];
        hasher.update(hash);
    }

    cachehog
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
    let cachehog = populate_cachehog(input, 145_728);

    // Step 1+2: calculate sha256 and expand data using Salsa20.
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
                let op = ((opcode >> (j * 8)) & 0xFF) & (OP_COUNT - 1);
                let cachehog_idx = ((i as usize * OP_PER_BRANCH as usize) + (j as usize)) * cachehog.len() % cachehog.len();
                tmp = match op {
                    0x00 => tmp.wrapping_add(tmp),                                 // +
                    0x01 => tmp.wrapping_sub(tmp ^ 97),                            // XOR and
                    0x02 => tmp.wrapping_mul(tmp),                                 // *
                    0x03 => tmp ^ data[pos2 as usize], // XOR with end of data
                    0x04 => tmp & data[pos2 as usize], // AND with end of data
                    0x05 => tmp ^ data[(pos2 as usize + pos1 as usize) / 2], // AND with midpoint of data
                    0x06 => !tmp,                                            // binary NOT operator
                    0x07 => tmp.wrapping_shl((tmp & 3) as u32),              // shift left
                    0x08 => tmp.wrapping_shr((tmp & 3) as u32),              // shift right
                    0x09 => tmp.reverse_bits(),                              // reverse bits
                    0x0A => tmp ^ tmp.count_ones() as u8,                    // ones count bits
                    0x0B => tmp.rotate_left(tmp as u32),                     // rotate left random
                    0x0C => tmp.rotate_left(1),                              // rotate left 1
                    0x0D => tmp.rotate_left(3),                              // rotate left 3
                    0x0E => tmp.rotate_left(5),                              // rotate left 5
                    0x0F => tmp.rotate_left(7),                              // rotate left 7
                    0x10 => tmp.rotate_right(tmp as u32),                    // rotate right random
                    0x11 => tmp.rotate_right(1),                             // rotate right 1
                    0x12 => tmp.rotate_right(3),                             // rotate right 3
                    0x13 => tmp.rotate_right(5),                             // rotate right 5
                    0x14 => tmp.rotate_right(7),                             // rotate right 7
                    0x15 => tmp ^ tmp.rotate_left(2),                        // rotate left 2, XOR
                    0x16 => tmp ^ tmp.rotate_left(4),                        // rotate left 4, XOR
                    0x17 => tmp ^ tmp.rotate_left(6),                        // rotate left 6, XOR
                    0x18 => tmp ^ tmp.rotate_right(2),                       // rotate right 2, XOR
                    0x19 => tmp ^ tmp.rotate_right(4),                       // rotate right 4, XOR
                    0x1A => tmp ^ tmp.rotate_right(6),                       // rotate right 6, XOR
                    0x1B => (tmp >> 4) | (tmp << 4),                         // swap nibbles
                    0x1C => ((tmp >> 1) & 0b01010101) | ((tmp << 1) & 0b10101010), // swap adjacent bits
                    0x1D => tmp ^ 0b01010101, // invert odd bits
                    0x1E => tmp ^ 0b10101010, // invert even bits
                    0x1F => (tmp >> 4).reverse_bits() | (tmp & 0x0F), // reverse left nibble
                    0x20 => (tmp >> 4) | (tmp & 0x0F).reverse_bits(), // reverse right nibble
                    0x21 => tmp.wrapping_mul((tmp.count_zeros() as u8).wrapping_add(1)),
                    0x22 => tmp.wrapping_mul((tmp.trailing_ones() as u8).wrapping_add(7)),
                    0x23 => tmp.wrapping_add(tmp.count_ones() as u8),
                    0x24 => tmp.wrapping_sub((tmp.leading_zeros() as u8).wrapping_mul(43)),
                    0x25 => (tmp >> 4) ^ 0b0101 | (tmp & 0x0F), // invert odd bits left nibble
                    0x26 => (tmp >> 4) | (tmp & 0x0F) ^ 0b0101, // invert odd bits right nibble
                    0x27 => (tmp >> 4) ^ 0b1010 | (tmp & 0x0F), // invert even bits left nibble
                    0x28 => (tmp >> 4) | (tmp & 0x0F) ^ 0b1010, // invert even bits right nibble
                    0x29 => (tmp >> 4).rotate_left(1) | (tmp & 0x0F), // rotate left 1 left nibble
                    0x2A => (tmp >> 4) | (tmp & 0x0F).rotate_left(1), // rotate left 1 bits right nibble
                    0x2B => (tmp >> 4).rotate_left(3) | (tmp & 0x0F), // rotate left 3 bits left nibble
                    0x2C => (tmp >> 4) | (tmp & 0x0F).rotate_left(3), // rotate left 3 bits right nibble
                    0x2D => (tmp >> 4).rotate_right(1) | (tmp & 0x0F), // rotate right 1 left nibble
                    0x2E => (tmp >> 4) | (tmp & 0x0F).rotate_right(1), // rotate right 1 bits right nibble
                    0x2F => (tmp >> 4).rotate_right(3) | (tmp & 0x0F), // rotate right 3 bits left nibble
                    0x30 => (tmp >> 4) | (tmp & 0x0F).rotate_right(3), // rotate right 3 bits right nibble
                    0x31 => (tmp >> 4).rotate_left(tmp as u32) | (tmp & 0x0F), // rotate left random left nibble
                    0x32 => (tmp >> 4) | (tmp & 0x0F).rotate_left(tmp as u32), // rotate left random right nibble
                    0x33 => (tmp >> 4).rotate_right(tmp as u32) | (tmp & 0x0F), // rotate random left nibble
                    0x34 => (tmp >> 4) | (tmp & 0x0F).rotate_right(tmp as u32), // rotate random bits right nibble
                    0x35 => (tmp >> 4) ^ data[pos2 as usize] | (tmp & 0x0F), // left nibble XOR with end of data
                    0x36 => (tmp >> 4) | (tmp & 0x0F) ^ data[pos2 as usize], // right nibble XOR with end of data
                    0x37 => (tmp >> 4) & data[pos2 as usize] | (tmp & 0x0F), // left nibble AND with end of data
                    0x38 => (tmp >> 4) | (tmp & 0x0F) & data[pos2 as usize], // right nibble AND with end of data
                    0x39 => (tmp >> 4).wrapping_add(tmp) | (tmp & 0x0F),     // left nibble +
                    0x3A => (tmp >> 4) | (tmp & 0x0F).wrapping_add(tmp),     // right nibble +
                    0x3B => (tmp >> 4).wrapping_mul(tmp) | (tmp & 0x0F),     // left nibble *
                    0x3C => (tmp >> 4) | (tmp & 0x0F).wrapping_mul(tmp),     // right nibble *
                    0x3D => tmp ^ data[pos1 as usize], // XOR with beginning of data
                    0x3E => tmp & data[pos1 as usize], // AND with beginning of data
                    0x3F => tmp.wrapping_mul(data[pos1 as usize]), // * with beginning of data

                    _ => unreachable!("Unknown branch reached with branch ID {:x}", op),
                }.wrapping_add(cachehog[cachehog_idx])
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