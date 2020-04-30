//! TransactionBroadcast message of the protocol version 2

use crate::message::Message;

use std::ops::Range;

const VARIABLE_MIN_SIZE: usize = 292;
const VARIABLE_MAX_SIZE: usize = 1604;

#[derive(Clone, Default)]
pub(crate) struct TransactionBroadcast {
    pub(crate) transaction: Vec<u8>,
}

impl TransactionBroadcast {
    pub(crate) fn new(transaction: &[u8]) -> Self {
        Self {
            transaction: transaction.to_vec(),
        }
    }
}

impl Message for TransactionBroadcast {
    const ID: u8 = 0x04;

    fn size_range() -> Range<usize> {
        (VARIABLE_MIN_SIZE)..(VARIABLE_MAX_SIZE + 1)
    }

    fn from_bytes(bytes: &[u8]) -> Self {
        let mut message = Self::default();

        message.transaction = bytes.to_vec();

        message
    }

    fn size(&self) -> usize {
        self.transaction.len()
    }

    fn to_bytes(self, bytes: &mut [u8]) {
        bytes.copy_from_slice(&self.transaction)
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    use crate::message::{
        Header,
        MessageError,
        Tlv,
        HEADER_SIZE,
    };

    use bee_test::slices::slice_eq;

    const TRANSACTION: [u8; 500] = [
        0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
        30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57,
        58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85,
        86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110,
        111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132,
        133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154,
        155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176,
        177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198,
        199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220,
        221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242,
        243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13,
        14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41,
        42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70,
        71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98,
        99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120,
        121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142,
        143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164,
        165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186,
        187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208,
        209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230,
        231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244,
    ];

    #[test]
    fn id() {
        assert_eq!(TransactionBroadcast::ID, 4);
    }

    #[test]
    fn size_range() {
        assert_eq!(TransactionBroadcast::size_range().contains(&291), false);
        assert_eq!(TransactionBroadcast::size_range().contains(&292), true);
        assert_eq!(TransactionBroadcast::size_range().contains(&293), true);

        assert_eq!(TransactionBroadcast::size_range().contains(&1603), true);
        assert_eq!(TransactionBroadcast::size_range().contains(&1604), true);
        assert_eq!(TransactionBroadcast::size_range().contains(&1605), false);
    }

    #[test]
    fn size() {
        let message = TransactionBroadcast::new(&TRANSACTION);

        assert_eq!(message.size(), 500);
    }

    fn to_from_eq(message: TransactionBroadcast) {
        assert_eq!(slice_eq(&message.transaction, &TRANSACTION), true);
    }

    #[test]
    fn to_from() {
        let message_from = TransactionBroadcast::new(&TRANSACTION);
        let mut bytes = vec![0u8; message_from.size()];

        message_from.to_bytes(&mut bytes);
        to_from_eq(TransactionBroadcast::from_bytes(&bytes));
    }

    #[test]
    fn tlv_invalid_length() {
        match Tlv::from_bytes::<TransactionBroadcast>(
            &Header {
                message_type: TransactionBroadcast::ID,
                message_length: 291,
            },
            &[0; 291],
        ) {
            Err(MessageError::InvalidPayloadLength(length)) => assert_eq!(length, 291),
            _ => unreachable!(),
        }
        match Tlv::from_bytes::<TransactionBroadcast>(
            &Header {
                message_type: TransactionBroadcast::ID,
                message_length: 1605,
            },
            &[0; 1605],
        ) {
            Err(MessageError::InvalidPayloadLength(length)) => assert_eq!(length, 1605),
            _ => unreachable!(),
        }
    }

    #[test]
    fn tlv() {
        let message_from = TransactionBroadcast::new(&TRANSACTION);
        let bytes = Tlv::into_bytes(message_from);

        to_from_eq(
            Tlv::from_bytes::<TransactionBroadcast>(&Header::from_bytes(&bytes[0..HEADER_SIZE]), &bytes[HEADER_SIZE..])
                .unwrap(),
        );
    }
}