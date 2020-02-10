use crate::messages::message::Message;

use std::ops::Range;

const _HANDSHAKE_TYPE_ID: u8 = 1;
const HANDSHAKE_COORDINATOR_SIZE: usize = 49;
const HANDSHAKE_CONSTANT_SIZE: usize = 2 + 8 + HANDSHAKE_COORDINATOR_SIZE + 1;
const HANDSHAKE_VARIABLE_MIN_SIZE: usize = 1;
const HANDSHAKE_VARIABLE_MAX_SIZE: usize = 32;

pub struct Handshake {
    port: u16,
    timestamp: u64,
    coordinator: [u8; HANDSHAKE_COORDINATOR_SIZE],
    minimum_weight_magnitude: u8,
    supported_messages: [u8; HANDSHAKE_VARIABLE_MAX_SIZE],
}

impl Handshake {
    pub fn new() -> Self {
        Self {
            port: 0,
            timestamp: 0,
            coordinator: [0; HANDSHAKE_COORDINATOR_SIZE],
            minimum_weight_magnitude: 0,
            supported_messages: [0; HANDSHAKE_VARIABLE_MAX_SIZE],
        }
    }
}

impl Message for Handshake {
    fn size_range() -> Range<usize> {
        (HANDSHAKE_CONSTANT_SIZE + HANDSHAKE_VARIABLE_MIN_SIZE)
            ..(HANDSHAKE_CONSTANT_SIZE + HANDSHAKE_VARIABLE_MAX_SIZE + 1)
    }

    fn from_bytes(_bytes: &[u8]) -> Self {
        Self {
            port: 0,
            timestamp: 0,
            coordinator: [0; HANDSHAKE_COORDINATOR_SIZE],
            minimum_weight_magnitude: 0,
            supported_messages: [0; HANDSHAKE_VARIABLE_MAX_SIZE],
        }
    }

    fn to_bytes(self) -> Vec<u8> {
        [].to_vec()
    }
}
