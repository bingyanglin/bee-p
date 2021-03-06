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

pub mod origin;
pub mod outbox;
pub mod store;
pub mod whitelist;
pub mod worker;

use crate::address::{
    url::{Protocol, Url},
    Address,
};

use std::fmt;

/// The id of an `Endpoint`.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct EndpointId {
    inner: Address,
}

impl From<Address> for EndpointId {
    fn from(addr: Address) -> Self {
        Self { inner: addr }
    }
}

impl From<Url> for EndpointId {
    fn from(url: Url) -> Self {
        match url {
            Url::Tcp(socket_addr) | Url::Udp(socket_addr) => Self { inner: socket_addr },
        }
    }
}

impl fmt::Display for EndpointId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inner)
    }
}

/// Represents an `Endpoint`.
#[derive(Clone, Debug)]
pub struct Endpoint {
    /// The id of the endpoint.
    pub id: EndpointId,

    /// The address of the endpoint.
    pub address: Address,

    /// The protocol used to communicate with that endpoint.
    pub protocol: Protocol,
}

impl Endpoint {
    /// Creates a new endpoint.
    pub fn new(address: Address, protocol: Protocol) -> Self {
        Self {
            id: address.into(),
            address,
            protocol,
        }
    }
    /// Creates an endpoint from a `Url`.
    pub fn from_url(url: Url) -> Self {
        let address = url.address();
        let protocol = url.protocol();

        Endpoint::new(address, protocol)
    }
}

impl Eq for Endpoint {}
impl PartialEq for Endpoint {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use async_std::task::block_on;

    #[test]
    fn create_epid_from_address() {
        let addr = block_on(Address::from_addr_str("127.0.0.1:16000")).unwrap();

        let epid: EndpointId = addr.into();

        assert_eq!("127.0.0.1:16000", epid.to_string());
    }

    #[test]
    fn create_epid_from_url() {
        let url = block_on(Url::from_url_str("tcp://[::1]:16000")).unwrap();

        let epid: EndpointId = url.into();
        assert_eq!("[::1]:16000", epid.to_string());
    }

    #[test]
    fn create_endpoint_from_url() {
        let url = block_on(Url::from_url_str("udp://[::1]:16000")).unwrap();
        let ep = Endpoint::from_url(url);

        assert_eq!("[::1]:16000", ep.id.to_string());
        assert_eq!(Protocol::Udp, ep.protocol);
        assert_eq!("[::1]:16000", ep.address.to_string());
    }
}
