use alloy_primitives::{hex, keccak256, Address, B256};
use clap::{Parser, Subcommand};
use k256::ecdsa::SigningKey;
use rand_core::OsRng;
use rayon::prelude::*;
use serde::Deserialize;
use std::fs;
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;

/// Deterministic Deployment Proxy address
/// https://github.com/Arachnid/deterministic-deployment-proxy
const DETERMINISTIC_DEPLOYER: Address = Address::new([
    0x4e, 0x59, 0xb4, 0x48, 0x47, 0xb3, 0x79, 0x57, 0x85, 0x88,
    0x92, 0x0c, 0xa7, 0x8f, 0xbf, 0x26, 0xc0, 0xb4, 0x95, 0x6c,
]);

/// Foundry artifact JSON structure
#[derive(Deserialize)]
struct FoundryArtifact {
    bytecode: BytecodeObject,
}

#[derive(Deserialize)]
struct BytecodeObject {
    object: String,
}

/// Single nibble requirement in a pattern
#[derive(Debug, Clone, Copy)]
struct NibbleReq {
    /// The nibble value (0-15), or None for wildcard
    value: Option<u8>,
    /// For letters (a-f), whether uppercase is required in checksum (true=upper, false=lower, None=don't care)
    checksum_upper: Option<bool>,
}

/// Pattern for matching addresses - stores expected nibbles where None means wildcard
#[derive(Debug, Clone)]
struct Pattern {
    /// Nibbles to match at start
    start: Vec<NibbleReq>,
    /// Nibbles to match at end
    end: Vec<NibbleReq>,
    /// Whether to enforce checksum matching
    checksum: bool,
}

impl Pattern {
    /// Parse a pattern string like "abc_4" into nibble requirements
    /// Preserves case information for checksum matching
    fn parse_hex_pattern(s: &str) -> Result<Vec<NibbleReq>, String> {
        let mut nibbles = Vec::with_capacity(s.len());

        for c in s.chars() {
            match c {
                '_' => nibbles.push(NibbleReq {
                    value: None,
                    checksum_upper: None,
                }),
                '0'..='9' => nibbles.push(NibbleReq {
                    value: Some(c as u8 - b'0'),
                    checksum_upper: None, // Numbers don't have case
                }),
                'a'..='f' => nibbles.push(NibbleReq {
                    value: Some(c as u8 - b'a' + 10),
                    checksum_upper: Some(false), // Lowercase
                }),
                'A'..='F' => nibbles.push(NibbleReq {
                    value: Some(c as u8 - b'A' + 10),
                    checksum_upper: Some(true), // Uppercase
                }),
                _ => return Err(format!("Invalid hex character: '{}'", c)),
            }
        }

        Ok(nibbles)
    }

    /// Parse from combined format: "0xabc_4...123" or "abc_4...123"
    fn from_combined(input: &str, checksum: bool) -> Result<Self, String> {
        let input = input.strip_prefix("0x").unwrap_or(input);
        let input = input.strip_prefix("0X").unwrap_or(input);

        // Split by "..."
        let parts: Vec<&str> = input.split("...").collect();

        match parts.len() {
            1 => {
                // Only start pattern, no "..."
                let start = Self::parse_hex_pattern(parts[0])?;
                if start.len() > 40 {
                    return Err("Start pattern exceeds 40 hex characters".to_string());
                }
                Ok(Pattern {
                    start,
                    end: Vec::new(),
                    checksum,
                })
            }
            2 => {
                let start = if parts[0].is_empty() {
                    Vec::new()
                } else {
                    Self::parse_hex_pattern(parts[0])?
                };
                let end = if parts[1].is_empty() {
                    Vec::new()
                } else {
                    Self::parse_hex_pattern(parts[1])?
                };

                if start.len() + end.len() > 40 {
                    return Err("Combined pattern exceeds 40 hex characters".to_string());
                }

                Ok(Pattern {
                    start,
                    end,
                    checksum,
                })
            }
            _ => Err("Pattern can only contain one '...' separator".to_string()),
        }
    }

    /// Create from separate start and end strings
    fn from_start_end(start: Option<&str>, end: Option<&str>, checksum: bool) -> Result<Self, String> {
        let start_nibbles = match start {
            Some(s) => {
                let s = s.strip_prefix("0x").unwrap_or(s);
                let s = s.strip_prefix("0X").unwrap_or(s);
                Self::parse_hex_pattern(s)?
            }
            None => Vec::new(),
        };

        let end_nibbles = match end {
            Some(s) => {
                let s = s.strip_prefix("0x").unwrap_or(s);
                let s = s.strip_prefix("0X").unwrap_or(s);
                Self::parse_hex_pattern(s)?
            }
            None => Vec::new(),
        };

        if start_nibbles.len() + end_nibbles.len() > 40 {
            return Err("Combined pattern exceeds 40 hex characters".to_string());
        }

        Ok(Pattern {
            start: start_nibbles,
            end: end_nibbles,
            checksum,
        })
    }

    /// Check if an address matches this pattern (without checksum)
    #[inline(always)]
    fn matches_value(&self, addr: &[u8; 20]) -> bool {
        // Check start pattern
        for (i, req) in self.start.iter().enumerate() {
            if let Some(nibble) = req.value {
                let byte = addr[i / 2];
                let actual = if i % 2 == 0 {
                    byte >> 4
                } else {
                    byte & 0x0F
                };
                if actual != nibble {
                    return false;
                }
            }
        }

        // Check end pattern
        let total_nibbles = 40;
        let end_start = total_nibbles - self.end.len();
        for (i, req) in self.end.iter().enumerate() {
            if let Some(nibble) = req.value {
                let pos = end_start + i;
                let byte = addr[pos / 2];
                let actual = if pos.is_multiple_of(2) {
                    byte >> 4
                } else {
                    byte & 0x0F
                };
                if actual != nibble {
                    return false;
                }
            }
        }

        true
    }

    /// Check if an address matches this pattern including checksum requirements
    #[inline(always)]
    fn matches(&self, addr: &[u8; 20]) -> bool {
        // First check values
        if !self.matches_value(addr) {
            return false;
        }

        // If checksum matching is not required, we're done
        if !self.checksum {
            return true;
        }

        // Calculate checksum hash for this address
        let addr_hex = hex::encode(addr);
        let checksum_hash = keccak256(addr_hex.as_bytes());

        // Check start pattern checksum requirements
        for (i, req) in self.start.iter().enumerate() {
            if let Some(expected_upper) = req.checksum_upper {
                // Get the corresponding nibble from the checksum hash
                let hash_byte = checksum_hash[i / 2];
                let hash_nibble = if i % 2 == 0 {
                    hash_byte >> 4
                } else {
                    hash_byte & 0x0F
                };
                // EIP-55: if hash nibble >= 8, the character should be uppercase
                let is_upper = hash_nibble >= 8;
                if is_upper != expected_upper {
                    return false;
                }
            }
        }

        // Check end pattern checksum requirements
        let total_nibbles = 40;
        let end_start = total_nibbles - self.end.len();
        for (i, req) in self.end.iter().enumerate() {
            if let Some(expected_upper) = req.checksum_upper {
                let pos = end_start + i;
                let hash_byte = checksum_hash[pos / 2];
                let hash_nibble = if pos.is_multiple_of(2) {
                    hash_byte >> 4
                } else {
                    hash_byte & 0x0F
                };
                let is_upper = hash_nibble >= 8;
                if is_upper != expected_upper {
                    return false;
                }
            }
        }

        true
    }

    fn display(&self) -> String {
        let mut result = String::from("0x");

        for req in &self.start {
            match req.value {
                Some(n) if n >= 10 => {
                    let c = if req.checksum_upper == Some(true) {
                        (b'A' + n - 10) as char
                    } else {
                        (b'a' + n - 10) as char
                    };
                    result.push(c);
                }
                Some(n) => result.push_str(&format!("{:x}", n)),
                None => result.push('_'),
            }
        }

        if !self.end.is_empty() {
            result.push_str("...");
            for req in &self.end {
                match req.value {
                    Some(n) if n >= 10 => {
                        let c = if req.checksum_upper == Some(true) {
                            (b'A' + n - 10) as char
                        } else {
                            (b'a' + n - 10) as char
                        };
                        result.push(c);
                    }
                    Some(n) => result.push_str(&format!("{:x}", n)),
                    None => result.push('_'),
                }
            }
        }

        if self.checksum {
            result.push_str(" (checksum)");
        }

        result
    }

    /// Count non-wildcard characters for difficulty estimation
    fn difficulty_count(&self) -> usize {
        self.start
            .iter()
            .chain(self.end.iter())
            .filter(|r| r.value.is_some())
            .count()
    }

    /// Count checksum-constrained characters for additional difficulty
    fn checksum_count(&self) -> usize {
        if !self.checksum {
            return 0;
        }
        self.start
            .iter()
            .chain(self.end.iter())
            .filter(|r| r.checksum_upper.is_some())
            .count()
    }
}

/// Calculate the CREATE contract address: keccak256(rlp([sender, nonce]))[12..]
/// RLP encoding is done manually for maximum performance
#[inline(always)]
fn calculate_create_address(sender: &Address, nonce: u64) -> Address {
    // For nonce 0: RLP([address, 0]) = 0xd6 0x94 <20 bytes address> 0x80
    // For nonce 1-127: RLP([address, n]) = 0xd6 0x94 <20 bytes address> <n>
    // For nonce 128-255: RLP([address, n]) = 0xd7 0x94 <20 bytes address> 0x81 <n>
    // For larger nonces, the encoding varies based on byte length

    let mut buf = Vec::with_capacity(32);

    if nonce == 0 {
        // List length = 1 (0x94) + 20 (address) + 1 (0x80) = 22 = 0xd6
        buf.push(0xd6);
        buf.push(0x94); // 0x80 + 20 = string of 20 bytes
        buf.extend_from_slice(sender.as_slice());
        buf.push(0x80); // empty string for nonce 0
    } else if nonce < 128 {
        // List length = 1 + 20 + 1 = 22 = 0xd6
        buf.push(0xd6);
        buf.push(0x94);
        buf.extend_from_slice(sender.as_slice());
        buf.push(nonce as u8);
    } else {
        // For larger nonces, encode based on byte length
        let nonce_bytes_full = nonce.to_be_bytes();
        let leading_zeros = nonce.leading_zeros() as usize / 8;
        let nonce_bytes = &nonce_bytes_full[leading_zeros..];
        let nonce_len = nonce_bytes.len();

        let list_len = 1 + 20 + 1 + nonce_len; // 0x94, address, 0x80+len, nonce bytes

        if list_len <= 55 {
            buf.push(0xc0 + list_len as u8);
        } else {
            // For very large nonces (extremely rare)
            let len_bytes_full = list_len.to_be_bytes();
            let len_leading_zeros = list_len.leading_zeros() as usize / 8;
            let len_bytes = &len_bytes_full[len_leading_zeros..];
            buf.push(0xf7 + len_bytes.len() as u8);
            buf.extend_from_slice(len_bytes);
        }

        buf.push(0x94);
        buf.extend_from_slice(sender.as_slice());
        buf.push(0x80 + nonce_len as u8);
        buf.extend_from_slice(nonce_bytes);
    }

    let hash = keccak256(&buf);
    Address::from_slice(&hash[12..])
}

/// Derive Ethereum address from a signing key
#[inline(always)]
fn derive_address(signing_key: &SigningKey) -> Address {
    let public_key = signing_key.verifying_key();
    let public_key_bytes = public_key.to_encoded_point(false);
    let public_key_slice = &public_key_bytes.as_bytes()[1..]; // Skip the 0x04 prefix

    let hash = keccak256(public_key_slice);
    Address::from_slice(&hash[12..])
}

/// Calculate the CREATE2 contract address: keccak256(0xff ++ deployer ++ salt ++ keccak256(init_code))[12..]
#[inline(always)]
fn calculate_create2_address(deployer: &Address, salt: &B256, init_code_hash: &B256) -> Address {
    let mut buf = [0u8; 85]; // 1 + 20 + 32 + 32
    buf[0] = 0xff;
    buf[1..21].copy_from_slice(deployer.as_slice());
    buf[21..53].copy_from_slice(salt.as_slice());
    buf[53..85].copy_from_slice(init_code_hash.as_slice());

    let hash = keccak256(buf);
    Address::from_slice(&hash[12..])
}

/// Load and parse init code from a Foundry artifact JSON file
fn load_init_code(path: &PathBuf) -> Result<Vec<u8>, String> {
    let content = fs::read_to_string(path)
        .map_err(|e| format!("Failed to read file: {}", e))?;

    let artifact: FoundryArtifact = serde_json::from_str(&content)
        .map_err(|e| format!("Failed to parse JSON: {}", e))?;

    let bytecode_str = artifact.bytecode.object
        .strip_prefix("0x")
        .unwrap_or(&artifact.bytecode.object);

    hex::decode(bytecode_str)
        .map_err(|e| format!("Failed to decode bytecode hex: {}", e))
}

/// Result of successful mining for wallet address
struct AddressMiningResult {
    private_key: B256,
    address: Address,
}

/// Result of successful mining for CREATE deployment
struct CreateMiningResult {
    private_key: B256,
    account_address: Address,
    contract_address: Address,
}

/// Result of successful mining for CREATE2 deployment
struct Create2MiningResult {
    salt: B256,
    contract_address: Address,
}

/// Mine for a vanity wallet address using parallel processing
fn mine_wallet_address(pattern: &Pattern) -> AddressMiningResult {
    let found = Arc::new(AtomicBool::new(false));
    let attempts = Arc::new(AtomicU64::new(0));

    let num_threads = rayon::current_num_threads();
    eprintln!("Mining with {} threads...", num_threads);
    eprintln!("Looking for pattern: {}", pattern.display());

    let result: Option<AddressMiningResult> = (0..num_threads)
        .into_par_iter()
        .find_map_any(|_| {
            let mut local_attempts = 0u64;

            loop {
                if found.load(Ordering::Relaxed) {
                    return None;
                }

                // Generate random private key using OS randomness (cryptographically secure)
                let signing_key = SigningKey::random(&mut OsRng);
                let address = derive_address(&signing_key);

                local_attempts += 1;

                // Periodically update global counter and check for found
                if local_attempts.is_multiple_of(10000) {
                    let total = attempts.fetch_add(10000, Ordering::Relaxed) + 10000;
                    // Adaptive logging: every 1M for first 10M, every 10M until 100M, then every 100M
                    let should_log = if total <= 10_000_000 {
                        total.is_multiple_of(1_000_000)
                    } else if total <= 100_000_000 {
                        total.is_multiple_of(10_000_000)
                    } else {
                        total.is_multiple_of(100_000_000)
                    };
                    if should_log {
                        eprintln!("Checked {} million addresses...", total / 1_000_000);
                    }
                }

                if pattern.matches(address.as_slice().try_into().unwrap()) {
                    found.store(true, Ordering::Relaxed);

                    let private_key_bytes = signing_key.to_bytes();
                    let private_key = B256::from_slice(&private_key_bytes);

                    return Some(AddressMiningResult {
                        private_key,
                        address,
                    });
                }
            }
        });

    result.expect("Mining should always find a result")
}

/// Mine for a vanity CREATE contract address using parallel processing
fn mine_create_address(pattern: &Pattern, nonce: u64) -> CreateMiningResult {
    let found = Arc::new(AtomicBool::new(false));
    let attempts = Arc::new(AtomicU64::new(0));

    let num_threads = rayon::current_num_threads();
    eprintln!("Mining with {} threads...", num_threads);
    eprintln!("Looking for pattern: {}", pattern.display());

    let result: Option<CreateMiningResult> = (0..num_threads)
        .into_par_iter()
        .find_map_any(|_| {
            let mut local_attempts = 0u64;

            loop {
                if found.load(Ordering::Relaxed) {
                    return None;
                }

                // Generate random private key using OS randomness (cryptographically secure)
                let signing_key = SigningKey::random(&mut OsRng);
                let account_address = derive_address(&signing_key);
                let contract_address = calculate_create_address(&account_address, nonce);

                local_attempts += 1;

                // Periodically update global counter and check for found
                if local_attempts.is_multiple_of(10000) {
                    let total = attempts.fetch_add(10000, Ordering::Relaxed) + 10000;
                    // Adaptive logging: every 1M for first 10M, every 10M until 100M, then every 100M
                    let should_log = if total <= 10_000_000 {
                        total.is_multiple_of(1_000_000)
                    } else if total <= 100_000_000 {
                        total.is_multiple_of(10_000_000)
                    } else {
                        total.is_multiple_of(100_000_000)
                    };
                    if should_log {
                        eprintln!("Checked {} million addresses...", total / 1_000_000);
                    }
                }

                if pattern.matches(contract_address.as_slice().try_into().unwrap()) {
                    found.store(true, Ordering::Relaxed);

                    let private_key_bytes = signing_key.to_bytes();
                    let private_key = B256::from_slice(&private_key_bytes);

                    return Some(CreateMiningResult {
                        private_key,
                        account_address,
                        contract_address,
                    });
                }
            }
        });

    result.expect("Mining should always find a result")
}

/// Mine for a CREATE2 salt that produces a matching contract address
fn mine_create2_salt(pattern: &Pattern, deployer: &Address, init_code_hash: &B256) -> Create2MiningResult {
    let found = Arc::new(AtomicBool::new(false));
    let attempts = Arc::new(AtomicU64::new(0));

    let num_threads = rayon::current_num_threads();
    eprintln!("Mining with {} threads...", num_threads);
    eprintln!("Looking for pattern: {}", pattern.display());
    eprintln!("Deployer: {}", deployer);
    eprintln!("Init code hash: 0x{}", hex::encode(init_code_hash));

    let result: Option<Create2MiningResult> = (0..num_threads)
        .into_par_iter()
        .find_map_any(|thread_idx| {
            let mut counter = 0u64;

            loop {
                if found.load(Ordering::Relaxed) {
                    return None;
                }

                // Generate salt from thread index and counter (faster than random)
                let mut salt_bytes = [0u8; 32];
                salt_bytes[0..8].copy_from_slice(&(thread_idx as u64).to_le_bytes());
                salt_bytes[8..16].copy_from_slice(&counter.to_le_bytes());
                let salt = B256::from(salt_bytes);
                counter += 1;

                let contract_address = calculate_create2_address(deployer, &salt, init_code_hash);

                // Periodically update global counter
                if counter.is_multiple_of(10000) {
                    let total = attempts.fetch_add(10000, Ordering::Relaxed) + 10000;
                    // Adaptive logging: every 1M for first 10M, every 10M until 100M, then every 100M
                    let should_log = if total <= 10_000_000 {
                        total.is_multiple_of(1_000_000)
                    } else if total <= 100_000_000 {
                        total.is_multiple_of(10_000_000)
                    } else {
                        total.is_multiple_of(100_000_000)
                    };
                    if should_log {
                        eprintln!("Checked {} million salts...", total / 1_000_000);
                    }
                }

                if pattern.matches(contract_address.as_slice().try_into().unwrap()) {
                    found.store(true, Ordering::Relaxed);

                    return Some(Create2MiningResult {
                        salt,
                        contract_address,
                    });
                }
            }
        });

    result.expect("Mining should always find a result")
}

#[derive(Parser)]
#[command(name = "eth-vanity")]
#[command(about = "Mine Ethereum vanity addresses")]
#[command(version)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Mine a vanity wallet address
    Address {
        /// Pattern to match (e.g., "0xabc_4...123")
        /// Use '_' for single character wildcard
        /// Use '...' to separate start and end patterns
        #[arg(conflicts_with_all = ["start", "end"])]
        pattern: Option<String>,

        /// Start pattern for the address
        #[arg(long)]
        start: Option<String>,

        /// End pattern for the address
        #[arg(long)]
        end: Option<String>,

        /// Enforce EIP-55 checksum matching on letter case
        /// e.g., "0xABc" requires A and B to be uppercase, c to be lowercase in checksum
        #[arg(long, alias = "case")]
        checksum: bool,
    },

    /// Mine a vanity address for CREATE contract deployment
    Create {
        /// Pattern to match (e.g., "0xabc_4...123")
        /// Use '_' for single character wildcard
        /// Use '...' to separate start and end patterns
        #[arg(conflicts_with_all = ["start", "end"])]
        pattern: Option<String>,

        /// Start pattern for the contract address
        #[arg(long)]
        start: Option<String>,

        /// End pattern for the contract address
        #[arg(long)]
        end: Option<String>,

        /// Enforce EIP-55 checksum matching on letter case
        /// e.g., "0xABc" requires A and B to be uppercase, c to be lowercase in checksum
        #[arg(long, alias = "case")]
        checksum: bool,
    },

    /// Mine a salt for CREATE2 deployment via deterministic deployment proxy
    Create2 {
        /// Path to Foundry artifact JSON file containing bytecode
        artifact: PathBuf,

        /// Pattern to match (e.g., "0xabc_4...123")
        /// Use '_' for single character wildcard
        /// Use '...' to separate start and end patterns
        #[arg(conflicts_with_all = ["start", "end"])]
        pattern: Option<String>,

        /// Start pattern for the contract address
        #[arg(long)]
        start: Option<String>,

        /// End pattern for the contract address
        #[arg(long)]
        end: Option<String>,

        /// Enforce EIP-55 checksum matching on letter case
        #[arg(long, alias = "case")]
        checksum: bool,

        /// Custom deployer address (default: 0x4e59b44847b379578588920cA78FbF26c0B4956C)
        #[arg(long)]
        deployer: Option<String>,
    },
}

fn parse_pattern(
    pattern: Option<String>,
    start: Option<String>,
    end: Option<String>,
    checksum: bool,
) -> Pattern {
    let parsed_pattern = if let Some(p) = pattern {
        Pattern::from_combined(&p, checksum)
    } else if start.is_some() || end.is_some() {
        Pattern::from_start_end(start.as_deref(), end.as_deref(), checksum)
    } else {
        eprintln!("Error: Must provide either a pattern or --start/--end flags");
        std::process::exit(1);
    };

    let pattern = match parsed_pattern {
        Ok(p) => p,
        Err(e) => {
            eprintln!("Error: {}", e);
            std::process::exit(1);
        }
    };

    if pattern.start.is_empty() && pattern.end.is_empty() {
        eprintln!("Error: Pattern cannot be empty");
        std::process::exit(1);
    }

    pattern
}

fn print_difficulty(pattern: &Pattern) {
    let hex_count = pattern.difficulty_count();
    let checksum_count = pattern.checksum_count();

    // Each hex char is 1/16, each checksum constraint is 1/2
    let expected_attempts = 16u64.pow(hex_count as u32) * 2u64.pow(checksum_count as u32);

    if checksum_count > 0 {
        eprintln!(
            "Expected attempts: ~{} (difficulty: {} hex chars + {} checksum constraints)",
            expected_attempts, hex_count, checksum_count
        );
    } else {
        eprintln!(
            "Expected attempts: ~{} (difficulty: {} hex chars)",
            expected_attempts, hex_count
        );
    }
}

fn main() {
    let cli = Cli::parse();

    match cli.command {
        Commands::Address {
            pattern,
            start,
            end,
            checksum,
        } => {
            let pattern = parse_pattern(pattern, start, end, checksum);
            print_difficulty(&pattern);

            let result = mine_wallet_address(&pattern);

            println!("\n=== FOUND ===");
            println!("Private Key: 0x{}", hex::encode(result.private_key));
            println!("Address:     {}", result.address);

            // Security reminder
            eprintln!("\nSECURITY: Store the private key securely and clear your terminal history!");
        }

        Commands::Create {
            pattern,
            start,
            end,
            checksum,
        } => {
            let pattern = parse_pattern(pattern, start, end, checksum);
            print_difficulty(&pattern);

            let result = mine_create_address(&pattern, 0);

            println!("\n=== FOUND ===");
            println!("Private Key:      0x{}", hex::encode(result.private_key));
            println!("Account Address:  {}", result.account_address);
            println!("Contract Address: {}", result.contract_address);

            // Security reminder
            eprintln!("\nSECURITY: Store the private key securely and clear your terminal history!");
        }

        Commands::Create2 {
            pattern,
            artifact,
            start,
            end,
            checksum,
            deployer,
        } => {
            let pattern = parse_pattern(pattern, start, end, checksum);
            print_difficulty(&pattern);

            // Load init code from artifact
            let init_code = match load_init_code(&artifact) {
                Ok(code) => code,
                Err(e) => {
                    eprintln!("Error loading artifact: {}", e);
                    std::process::exit(1);
                }
            };

            if init_code.is_empty() {
                eprintln!("Error: Bytecode is empty");
                std::process::exit(1);
            }

            eprintln!("Loaded bytecode: {} bytes", init_code.len());

            // Hash the init code
            let init_code_hash = keccak256(&init_code);

            // Parse deployer address or use default
            let deployer_addr = match deployer {
                Some(addr_str) => {
                    let addr_str = addr_str.strip_prefix("0x").unwrap_or(&addr_str);
                    match hex::decode(addr_str) {
                        Ok(bytes) if bytes.len() == 20 => {
                            Address::from_slice(&bytes)
                        }
                        _ => {
                            eprintln!("Error: Invalid deployer address");
                            std::process::exit(1);
                        }
                    }
                }
                None => DETERMINISTIC_DEPLOYER,
            };

            let result = mine_create2_salt(&pattern, &deployer_addr, &init_code_hash);

            println!("\n=== FOUND ===");
            println!("Salt:             0x{}", hex::encode(result.salt));
            println!("Contract Address: {}", result.contract_address);
            println!("Deployer:         {}", deployer_addr);
            println!("Init Code Hash:   0x{}", hex::encode(init_code_hash));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pattern_parsing_simple() {
        let pattern = Pattern::from_combined("abc", false).unwrap();
        assert_eq!(pattern.start.len(), 3);
        assert_eq!(pattern.start[0].value, Some(0xa));
        assert_eq!(pattern.start[1].value, Some(0xb));
        assert_eq!(pattern.start[2].value, Some(0xc));
    }

    #[test]
    fn test_pattern_parsing_with_wildcard() {
        let pattern = Pattern::from_combined("a_c", false).unwrap();
        assert_eq!(pattern.start[0].value, Some(0xa));
        assert_eq!(pattern.start[1].value, None);
        assert_eq!(pattern.start[2].value, Some(0xc));
    }

    #[test]
    fn test_pattern_parsing_with_prefix() {
        let pattern = Pattern::from_combined("0xABC", false).unwrap();
        assert_eq!(pattern.start.len(), 3);
        assert_eq!(pattern.start[0].value, Some(0xa));
    }

    #[test]
    fn test_pattern_parsing_start_end() {
        let pattern = Pattern::from_combined("abc...123", false).unwrap();
        assert_eq!(pattern.start.len(), 3);
        assert_eq!(pattern.end.len(), 3);
        assert_eq!(pattern.end[0].value, Some(1));
        assert_eq!(pattern.end[1].value, Some(2));
        assert_eq!(pattern.end[2].value, Some(3));
    }

    #[test]
    fn test_pattern_from_flags() {
        let pattern = Pattern::from_start_end(Some("abc"), Some("123"), false).unwrap();
        assert_eq!(pattern.start.len(), 3);
        assert_eq!(pattern.end.len(), 3);
    }

    #[test]
    fn test_invalid_hex() {
        assert!(Pattern::from_combined("xyz", false).is_err());
        assert!(Pattern::from_combined("abg", false).is_err());
    }

    #[test]
    fn test_pattern_matching() {
        let pattern = Pattern::from_combined("dead", false).unwrap();
        let matching_addr: [u8; 20] = [
            0xde, 0xad, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ];
        let non_matching_addr: [u8; 20] = [
            0xbe, 0xef, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ];
        assert!(pattern.matches(&matching_addr));
        assert!(!pattern.matches(&non_matching_addr));
    }

    #[test]
    fn test_pattern_matching_end() {
        let pattern = Pattern::from_combined("...beef", false).unwrap();
        let matching_addr: [u8; 20] = [
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0xbe, 0xef,
        ];
        assert!(pattern.matches(&matching_addr));
    }

    #[test]
    fn test_pattern_matching_wildcard() {
        let pattern = Pattern::from_combined("de_d", false).unwrap();
        let addr1: [u8; 20] = [
            0xde, 0xad, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ];
        let addr2: [u8; 20] = [
            0xde, 0x0d, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ];
        assert!(pattern.matches(&addr1));
        assert!(pattern.matches(&addr2));
    }

    #[test]
    fn test_create_address_calculation() {
        // Known test vector
        let sender = "0x6ac7ea33f8831ea9dcc53393aaa88b25a785dbf0"
            .parse::<Address>()
            .unwrap();
        let expected = "0xcd234a471b72ba2f1ccf0a70fcaba648a5eecd8d"
            .parse::<Address>()
            .unwrap();
        let calculated = calculate_create_address(&sender, 0);
        assert_eq!(calculated, expected);
    }

    #[test]
    fn test_create_address_nonce_1() {
        let sender = "0x6ac7ea33f8831ea9dcc53393aaa88b25a785dbf0"
            .parse::<Address>()
            .unwrap();
        let expected = "0x343c43a37d37dff08ae8c4a11544c718abb4fcf8"
            .parse::<Address>()
            .unwrap();
        let calculated = calculate_create_address(&sender, 1);
        assert_eq!(calculated, expected);
    }

    #[test]
    fn test_checksum_case_tracking() {
        // Test that case is properly tracked
        let pattern = Pattern::from_combined("AbC", true).unwrap();
        assert_eq!(pattern.start[0].value, Some(0xa));
        assert_eq!(pattern.start[0].checksum_upper, Some(true)); // A is uppercase
        assert_eq!(pattern.start[1].value, Some(0xb));
        assert_eq!(pattern.start[1].checksum_upper, Some(false)); // b is lowercase
        assert_eq!(pattern.start[2].value, Some(0xc));
        assert_eq!(pattern.start[2].checksum_upper, Some(true)); // C is uppercase
    }

    #[test]
    fn test_checksum_matching() {
        // Test address: 0x5aAeb6053F3E94C9b9A09f33669435E7Ef1BeAed (EIP-55 checksum example)
        // The checksum for this address has specific case requirements
        let addr: [u8; 20] = [
            0x5a, 0xae, 0xb6, 0x05, 0x3f, 0x3e, 0x94, 0xc9, 0xb9, 0xa0,
            0x9f, 0x33, 0x66, 0x94, 0x35, 0xe7, 0xef, 0x1b, 0xea, 0xed,
        ];

        // Without checksum, any case should match
        let pattern_no_checksum = Pattern::from_combined("5aae", false).unwrap();
        assert!(pattern_no_checksum.matches(&addr));

        let pattern_no_checksum2 = Pattern::from_combined("5AAE", false).unwrap();
        assert!(pattern_no_checksum2.matches(&addr));

        // With checksum enabled, only correct case should match
        // The checksum for 5aaeb6... should be 5aAeb6... (lowercase a, uppercase A, lowercase e, lowercase b)
        let pattern_correct = Pattern::from_combined("5aAe", true).unwrap();
        assert!(pattern_correct.matches(&addr));

        // Wrong case should not match with checksum enabled
        let pattern_wrong = Pattern::from_combined("5Aae", true).unwrap();
        assert!(!pattern_wrong.matches(&addr));
    }

    #[test]
    fn test_difficulty_counting() {
        let pattern = Pattern::from_combined("AbC123", true).unwrap();
        assert_eq!(pattern.difficulty_count(), 6); // All 6 are non-wildcard
        assert_eq!(pattern.checksum_count(), 3); // A, b, C have checksum constraints

        let pattern2 = Pattern::from_combined("A_C", true).unwrap();
        assert_eq!(pattern2.difficulty_count(), 2); // A and C
        assert_eq!(pattern2.checksum_count(), 2); // A and C
    }

    #[test]
    fn test_create2_address_calculation() {
        // Test vector from EIP-1014
        // deployer: 0x0000000000000000000000000000000000000000
        // salt: 0x0000000000000000000000000000000000000000000000000000000000000000
        // init_code: 0x00 (keccak256 = 0xbc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a)
        let deployer = Address::ZERO;
        let salt = B256::ZERO;
        let init_code_hash: B256 = "0xbc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a"
            .parse()
            .unwrap();
        let expected: Address = "0x4D1A2e2bB4F88F0250f26Ffff098B0b30B26BF38"
            .parse()
            .unwrap();

        let calculated = calculate_create2_address(&deployer, &salt, &init_code_hash);
        assert_eq!(calculated, expected);
    }

    #[test]
    fn test_create2_with_deterministic_proxy() {
        // Test with the deterministic deployment proxy address
        let deployer = DETERMINISTIC_DEPLOYER;
        let salt = B256::ZERO;
        // keccak256(0x) = keccak256 of empty bytes
        let init_code_hash = keccak256(&[]);

        let result = calculate_create2_address(&deployer, &salt, &init_code_hash);
        // Just verify it produces a valid address (20 bytes)
        assert_eq!(result.as_slice().len(), 20);
    }
}
