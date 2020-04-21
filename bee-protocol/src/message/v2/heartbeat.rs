use crate::{
    message::{
        Message,
        MessageError,
    },
    milestone::MilestoneIndex,
};

use std::{
    convert::TryInto,
    mem::size_of,
    ops::Range,
};

const HEARTBEAT_SOLID_MILESTONE_INDEX_SIZE: usize = size_of::<MilestoneIndex>();
const HEARTBEAT_SNAPSHOT_MILESTONE_INDEX_SIZE: usize = size_of::<MilestoneIndex>();
const HEARTBEAT_CONSTANT_SIZE: usize = HEARTBEAT_SOLID_MILESTONE_INDEX_SIZE + HEARTBEAT_SNAPSHOT_MILESTONE_INDEX_SIZE;

#[derive(Clone, Default)]
pub(crate) struct Heartbeat {
    pub(crate) solid_milestone_index: MilestoneIndex,
    pub(crate) snapshot_milestone_index: MilestoneIndex,
}

impl Heartbeat {
    pub(crate) fn new(solid_milestone_index: MilestoneIndex, snapshot_milestone_index: MilestoneIndex) -> Self {
        Self {
            solid_milestone_index: solid_milestone_index,
            snapshot_milestone_index: snapshot_milestone_index,
        }
    }
}

impl Message for Heartbeat {
    const ID: u8 = 0x06;

    fn size_range() -> Range<usize> {
        (HEARTBEAT_CONSTANT_SIZE)..(HEARTBEAT_CONSTANT_SIZE + 1)
    }

    fn from_bytes(bytes: &[u8]) -> Result<Self, MessageError> {
        if !Self::size_range().contains(&bytes.len()) {
            Err(MessageError::InvalidPayloadLength(bytes.len()))?;
        }

        let mut message = Self::default();
        let mut offset = 0;

        message.solid_milestone_index = MilestoneIndex::from_be_bytes(
            bytes[offset..offset + HEARTBEAT_SOLID_MILESTONE_INDEX_SIZE]
                .try_into()
                .map_err(|_| MessageError::InvalidPayloadField)?,
        );
        offset += HEARTBEAT_SOLID_MILESTONE_INDEX_SIZE;

        message.snapshot_milestone_index = MilestoneIndex::from_be_bytes(
            bytes[offset..offset + HEARTBEAT_SNAPSHOT_MILESTONE_INDEX_SIZE]
                .try_into()
                .map_err(|_| MessageError::InvalidPayloadField)?,
        );

        Ok(message)
    }

    fn size(&self) -> usize {
        HEARTBEAT_CONSTANT_SIZE
    }

    fn to_bytes(self, bytes: &mut [u8]) {
        bytes[0..HEARTBEAT_SOLID_MILESTONE_INDEX_SIZE].copy_from_slice(&self.solid_milestone_index.to_be_bytes());
        bytes[HEARTBEAT_SOLID_MILESTONE_INDEX_SIZE..].copy_from_slice(&self.snapshot_milestone_index.to_be_bytes());
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    use crate::message::{
        Header,
        HEADER_SIZE,
    };

    const FIRST_SOLID_MILESTONE_INDEX: MilestoneIndex = 0x3dc297b4;
    const LAST_SOLID_MILESTONE_INDEX: MilestoneIndex = 0x01181f9b;

    #[test]
    fn size_range_test() {
        assert_eq!(Heartbeat::size_range().contains(&7), false);
        assert_eq!(Heartbeat::size_range().contains(&8), true);
        assert_eq!(Heartbeat::size_range().contains(&9), false);
    }

    #[test]
    fn from_bytes_invalid_length_test() {
        match Heartbeat::from_bytes(&[0; 7]) {
            Err(MessageError::InvalidPayloadLength(length)) => assert_eq!(length, 7),
            _ => unreachable!(),
        }
        match Heartbeat::from_bytes(&[0; 9]) {
            Err(MessageError::InvalidPayloadLength(length)) => assert_eq!(length, 9),
            _ => unreachable!(),
        }
    }

    #[test]
    fn size_test() {
        let message = Heartbeat::new(FIRST_SOLID_MILESTONE_INDEX, LAST_SOLID_MILESTONE_INDEX);

        assert_eq!(message.size(), HEARTBEAT_CONSTANT_SIZE);
    }

    fn to_from_eq(message: Heartbeat) {
        assert_eq!(message.solid_milestone_index, FIRST_SOLID_MILESTONE_INDEX);
        assert_eq!(message.snapshot_milestone_index, LAST_SOLID_MILESTONE_INDEX);
    }

    #[test]
    fn to_from_test() {
        let message_from = Heartbeat::new(FIRST_SOLID_MILESTONE_INDEX, LAST_SOLID_MILESTONE_INDEX);
        let mut bytes = vec![0u8; message_from.size()];

        message_from.to_bytes(&mut bytes);
        to_from_eq(Heartbeat::from_bytes(&bytes).unwrap());
    }

    #[test]
    fn full_to_from_test() {
        let message_from = Heartbeat::new(FIRST_SOLID_MILESTONE_INDEX, LAST_SOLID_MILESTONE_INDEX);
        let bytes = message_from.into_full_bytes();

        to_from_eq(
            Heartbeat::from_full_bytes(&Header::from_bytes(&bytes[0..HEADER_SIZE]), &bytes[HEADER_SIZE..]).unwrap(),
        );
    }
}
