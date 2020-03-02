use crate::message::{
    Handshake, Heartbeat, LegacyGossip, MilestoneRequest, TransactionBroadcast, TransactionRequest,
};

// TODO channels ?
use crate::neighbor::{
    Neighbor, NeighborChannels, NeighborConnectedReceiverActorState, NeighborEvent,
    NeighborReceiverActor,
};
use crate::node::NodeMetrics;

use netzwerk::Command::AddPeer;
use netzwerk::{Address, Config, Event, EventSubscriber, Network, Peer, PeerId, Shutdown};

use std::collections::HashMap;

// TODO remove
use async_std::net::{Ipv4Addr, Ipv6Addr, SocketAddr, SocketAddrV4, SocketAddrV6, ToSocketAddrs};

use async_std::task::{block_on, spawn};
use futures::channel::mpsc::{channel, SendError, Sender};
use futures::sink::SinkExt;
use futures::stream::StreamExt;
use log::*;

pub struct Node {
    config: Config,
    network: Network,
    shutdown: Shutdown,
    events: EventSubscriber,
    // TODO thread-safety
    // TODO PeerID
    // neighbors: HashMap<PeerId, Neighbor>,
    neighbors: HashMap<PeerId, Sender<NeighborEvent>>,
    metrics: NodeMetrics,
}

impl Node {
    pub fn new(
        config: Config,
        network: Network,
        shutdown: Shutdown,
        events: EventSubscriber,
    ) -> Self {
        Self {
            network: network,
            shutdown: shutdown,
            events: events,
            config: config,
            neighbors: HashMap::new(),
            metrics: NodeMetrics::default(),
        }
    }

    async fn actor(mut self) {
        info!("[Node ] Starting actor");
        while let Some(event) = self.events.next().await {
            info!("[Node ] Received event {:?}", event);
            match event {
                Event::PeerAdded { peer_id, num_peers } => {
                    let (sender, receiver) = channel(1000);

                    self.neighbors.insert(peer_id, sender);

                    spawn(
                        NeighborReceiverActor::new(
                            peer_id,
                            receiver,
                            NeighborConnectedReceiverActorState {
                                network: self.network.clone(),
                            },
                        )
                        .run(),
                    );
                }
                Event::PeerRemoved { peer_id, num_peers } => {}
                Event::PeerConnected { peer_id } => {
                    if let Some(sender) = self.neighbors.get_mut(&peer_id) {
                        sender.send(NeighborEvent::Connected).await;
                    }
                }
                Event::PeerDisconnected { peer_id, reconnect } => {}
                Event::BytesReceived {
                    peer_id,
                    num_bytes,
                    from,
                    bytes,
                } => {
                    if let Some(sender) = self.neighbors.get_mut(&peer_id) {
                        sender
                            .send(NeighborEvent::Message {
                                size: num_bytes,
                                bytes: bytes,
                            })
                            .await;
                    }
                }
                _ => (),
            }
        }
    }

    // fn peer_added(&mut self, id: PeerId) {
    //     let channels = NeighborChannels::new();
    //     let neighbor = Neighbor::new(channels.senders);
    //
    //     // TODO check return
    //     self.neighbors.insert(id, neighbor);
    // }
    //
    // fn peer_removed(&mut self, id: PeerId) {
    //     // TODO check return
    //     self.neighbors.remove(&id);
    // }
    //
    // fn peer_connected(&self, id: PeerId) {
    //     if let Some(neighbor) = self.neighbors.get(&id) {
    //         spawn(neighbor.receive_actor());
    //     }
    //     // spawn(Neighbor::actor::<Handshake>(channels.receivers.handshake));
    //     // spawn(Neighbor::actor::<LegacyGossip>(
    //     //     channels.receivers.legacy_gossip,
    //     // ));
    //     // spawn(Neighbor::actor::<MilestoneRequest>(
    //     //     channels.receivers.milestone_request,
    //     // ));
    //     // spawn(Neighbor::actor::<TransactionBroadcast>(
    //     //     channels.receivers.transaction_broadcast,
    //     // ));
    //     // spawn(Neighbor::actor::<TransactionRequest>(
    //     //     channels.receivers.transaction_request,
    //     // ));
    //     // spawn(Neighbor::actor::<Heartbeat>(channels.receivers.heartbeat));
    // }
    //
    // fn peer_disconnected(&mut self, id: PeerId) {}

    pub fn start(self) {
        // spawn(Self::actor(self));
        block_on(Self::actor(self));
    }

    pub async fn init(&mut self) {
        info!("[Node ] Initializing...");

        for peer in self.config.peers().values() {
            self.add_peer(peer.clone()).await;
        }

        info!("[Node ] Initialized");
    }

    pub async fn add_peer(&mut self, peer: Peer) {
        self.network.send(AddPeer { peer }).await;
    }

    async fn send_handshake(
        &self,
        neighbor: &mut Neighbor,
        handshake: Handshake,
    ) -> Result<(), SendError> {
        let res = neighbor.senders.handshake.send(handshake).await;

        if res.is_ok() {
            neighbor.metrics.handshake_sent_inc();
            self.metrics.handshake_sent_inc();
        }

        res
    }

    async fn send_legacy_gossip(
        &self,
        neighbor: &mut Neighbor,
        legacy_gossip: LegacyGossip,
    ) -> Result<(), SendError> {
        let res = neighbor.senders.legacy_gossip.send(legacy_gossip).await;

        if res.is_ok() {
            neighbor.metrics.transactions_sent_inc();
            neighbor.metrics.legacy_gossip_sent_inc();
            self.metrics.transactions_sent_inc();
            self.metrics.legacy_gossip_sent_inc();
        }

        res
    }

    async fn send_milestone_request(
        &self,
        neighbor: &mut Neighbor,
        milestone_request: MilestoneRequest,
    ) -> Result<(), SendError> {
        let res = neighbor
            .senders
            .milestone_request
            .send(milestone_request)
            .await;

        if res.is_ok() {
            neighbor.metrics.milestone_request_sent_inc();
            self.metrics.milestone_request_sent_inc();
        }

        res
    }

    async fn send_transaction_broadcast(
        &self,
        neighbor: &mut Neighbor,
        transaction_broadcast: TransactionBroadcast,
    ) -> Result<(), SendError> {
        let res = neighbor
            .senders
            .transaction_broadcast
            .send(transaction_broadcast)
            .await;

        if res.is_ok() {
            neighbor.metrics.transactions_sent_inc();
            neighbor.metrics.transaction_broadcast_sent_inc();
            self.metrics.transactions_sent_inc();
            self.metrics.transaction_broadcast_sent_inc();
        }

        res
    }

    async fn send_transaction_request(
        &self,
        neighbor: &mut Neighbor,
        transaction_request: TransactionRequest,
    ) -> Result<(), SendError> {
        let res = neighbor
            .senders
            .transaction_request
            .send(transaction_request)
            .await;

        if res.is_ok() {
            neighbor.metrics.transaction_request_sent_inc();
            self.metrics.transaction_request_sent_inc();
        }

        res
    }

    async fn send_heartbeat(
        &self,
        neighbor: &mut Neighbor,
        heartbeat: Heartbeat,
    ) -> Result<(), SendError> {
        let res = neighbor.senders.heartbeat.send(heartbeat).await;

        if res.is_ok() {
            neighbor.metrics.heartbeat_sent_inc();
            self.metrics.heartbeat_sent_inc();
        }

        res
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use futures::stream::{Stream, StreamExt};

    // #[test]
    // fn send_handshake_test() {
    //     let node = Node::new();
    //     let mut channels = NeighborChannels::new();
    //     let mut neighbor = Neighbor::new(channels.senders);
    //
    //     assert_eq!(node.metrics.handshake_sent(), 0);
    //     assert_eq!(neighbor.metrics.handshake_sent(), 0);
    //
    //     assert!(channels.receivers.handshake.try_next().is_err());
    //     assert!(block_on(node.send_handshake(&mut neighbor, Handshake::default())).is_ok());
    //     assert!(block_on(channels.receivers.handshake.next()).is_some());
    //
    //     assert_eq!(node.metrics.handshake_sent(), 1);
    //     assert_eq!(neighbor.metrics.handshake_sent(), 1);
    // }
    //
    // #[test]
    // fn send_legacy_gossip_test() {
    //     let node = Node::new();
    //     let mut channels = NeighborChannels::new();
    //     let mut neighbor = Neighbor::new(channels.senders);
    //
    //     assert_eq!(node.metrics.legacy_gossip_sent(), 0);
    //     assert_eq!(node.metrics.transactions_sent(), 0);
    //     assert_eq!(neighbor.metrics.legacy_gossip_sent(), 0);
    //     assert_eq!(neighbor.metrics.transactions_sent(), 0);
    //
    //     assert!(channels.receivers.legacy_gossip.try_next().is_err());
    //     assert!(block_on(node.send_legacy_gossip(&mut neighbor, LegacyGossip::default())).is_ok());
    //     assert!(block_on(channels.receivers.legacy_gossip.next()).is_some());
    //
    //     assert_eq!(node.metrics.legacy_gossip_sent(), 1);
    //     assert_eq!(node.metrics.transactions_sent(), 1);
    //     assert_eq!(neighbor.metrics.legacy_gossip_sent(), 1);
    //     assert_eq!(neighbor.metrics.transactions_sent(), 1);
    // }
    //
    // #[test]
    // fn send_milestone_request_test() {
    //     let node = Node::new();
    //     let mut channels = NeighborChannels::new();
    //     let mut neighbor = Neighbor::new(channels.senders);
    //
    //     assert_eq!(node.metrics.milestone_request_sent(), 0);
    //     assert_eq!(neighbor.metrics.milestone_request_sent(), 0);
    //
    //     assert!(channels.receivers.milestone_request.try_next().is_err());
    //     assert!(
    //         block_on(node.send_milestone_request(&mut neighbor, MilestoneRequest::default()))
    //             .is_ok()
    //     );
    //     assert!(block_on(channels.receivers.milestone_request.next()).is_some());
    //
    //     assert_eq!(node.metrics.milestone_request_sent(), 1);
    //     assert_eq!(neighbor.metrics.milestone_request_sent(), 1);
    // }
    //
    // #[test]
    // fn send_transaction_broadcast_test() {
    //     let node = Node::new();
    //     let mut channels = NeighborChannels::new();
    //     let mut neighbor = Neighbor::new(channels.senders);
    //
    //     assert_eq!(node.metrics.transaction_broadcast_sent(), 0);
    //     assert_eq!(node.metrics.transactions_sent(), 0);
    //     assert_eq!(neighbor.metrics.transaction_broadcast_sent(), 0);
    //     assert_eq!(neighbor.metrics.transactions_sent(), 0);
    //
    //     assert!(channels.receivers.transaction_broadcast.try_next().is_err());
    //     assert!(block_on(
    //         node.send_transaction_broadcast(&mut neighbor, TransactionBroadcast::default())
    //     )
    //     .is_ok());
    //     assert!(block_on(channels.receivers.transaction_broadcast.next()).is_some());
    //
    //     assert_eq!(node.metrics.transaction_broadcast_sent(), 1);
    //     assert_eq!(node.metrics.transactions_sent(), 1);
    //     assert_eq!(neighbor.metrics.transaction_broadcast_sent(), 1);
    //     assert_eq!(neighbor.metrics.transactions_sent(), 1);
    // }
    //
    // #[test]
    // fn send_transaction_request_test() {
    //     let node = Node::new();
    //     let mut channels = NeighborChannels::new();
    //     let mut neighbor = Neighbor::new(channels.senders);
    //
    //     assert_eq!(node.metrics.transaction_request_sent(), 0);
    //     assert_eq!(neighbor.metrics.transaction_request_sent(), 0);
    //
    //     assert!(channels.receivers.transaction_request.try_next().is_err());
    //     assert!(block_on(
    //         node.send_transaction_request(&mut neighbor, TransactionRequest::default())
    //     )
    //     .is_ok());
    //     assert!(block_on(channels.receivers.transaction_request.next()).is_some());
    //
    //     assert_eq!(node.metrics.transaction_request_sent(), 1);
    //     assert_eq!(neighbor.metrics.transaction_request_sent(), 1);
    // }
    //
    // #[test]
    // fn send_heartbeat_test() {
    //     let node = Node::new();
    //     let mut channels = NeighborChannels::new();
    //     let mut neighbor = Neighbor::new(channels.senders);
    //
    //     assert_eq!(node.metrics.heartbeat_sent(), 0);
    //     assert_eq!(neighbor.metrics.heartbeat_sent(), 0);
    //
    //     assert!(channels.receivers.heartbeat.try_next().is_err());
    //     assert!(block_on(node.send_heartbeat(&mut neighbor, Heartbeat::default())).is_ok());
    //     assert!(block_on(channels.receivers.heartbeat.next()).is_some());
    //
    //     assert_eq!(node.metrics.heartbeat_sent(), 1);
    //     assert_eq!(neighbor.metrics.heartbeat_sent(), 1);
    // }
}