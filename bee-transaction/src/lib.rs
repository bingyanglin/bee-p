// Copyright 2020 IOTA Stiftung
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with
// the License. You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and limitations under the License.

#[macro_use]
extern crate serde;

mod bundled;
mod constants;
mod vertex;

pub use bundled::{
    Address, Bundle, BundledTransaction, BundledTransactionBuilder, BundledTransactionBuilders,
    BundledTransactionError, BundledTransactionField, BundledTransactions, Hash, IncomingBundleBuilder,
    IncomingBundleBuilderError, Index, Nonce, OutgoingBundleBuilder, OutgoingBundleBuilderError, Payload, Tag,
    Timestamp, Value,
};
pub use constants::{
    ADDRESS_TRIT_LEN, HASH_TRIT_LEN, NONCE_TRIT_LEN, PAYLOAD_TRIT_LEN, TAG_TRIT_LEN, TRANSACTION_BYTE_LEN,
    TRANSACTION_TRIT_LEN, TRANSACTION_TRYT_LEN,
};

pub use vertex::TransactionVertex;