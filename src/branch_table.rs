use sha2::{Digest, Sha512};
pub fn populate_branch_table(input: &[u8]) -> [u64; 4096] {
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
