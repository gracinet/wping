#![allow(unknown_lints)]
#![allow(match_bool)]

extern crate argparse;
extern crate byteorder;
extern crate chrono;
extern crate pnet;
extern crate pnet_macros_support;
extern crate libc;
extern crate num;
extern crate resolve;
use pnet::packet::ip::{IpNextHeaderProtocols};
use pnet::transport::{ TransportSender, TransportReceiver,
                       transport_channel,ipv4_packet_iter,
                       icmpv6_packet_iter};
use pnet::transport::TransportChannelType::{Layer3, Layer4};
use pnet::transport::TransportProtocol;
use pnet::packet::{Packet, MutablePacket};
use pnet::packet::ipv4::{MutableIpv4Packet, Ipv4Flags};
use pnet::packet::ipv6::Ipv6Packet;
use pnet::packet::icmp::{IcmpPacket, IcmpCode, IcmpTypes};
use pnet::packet::icmpv6::{self, Icmpv6Packet, Icmpv6Code, Icmpv6Types};
use pnet::packet::icmp::echo_request::{MutableEchoRequestPacket};
use pnet::packet::icmp::echo_reply::{EchoReplyPacket};
use pnet::packet::icmp;
use pnet_macros_support::packet::PacketSize;

// checksum
use pnet_macros_support::types::u16be;

use std::net::{Ipv4Addr, Ipv6Addr, IpAddr};
use std::str::FromStr;
use std::thread;
use std::time::{Duration, Instant};
use std::io::prelude::*;
use std::collections::vec_deque::VecDeque;
use num::pow::pow;
use libc::getpid;
use resolve::resolver::resolve_host;
use std::error::Error;
use std::fmt;
use std::mem;
use std::num::ParseIntError;
use std::u8;
use std::ops::Sub;
use std::iter::Iterator;
use byteorder::{BigEndian, WriteBytesExt};
use chrono::offset::local::Local;

use std::sync::mpsc::{self, RecvTimeoutError};

use argparse::{ArgumentParser, StoreOption, StoreTrue};

mod ewma;
mod columnar;
mod icmpv6_echo;

use columnar::{Columnar, Column};

use ewma::Ewma;

use icmpv6_echo::echo_reply::EchoReplyPacket as Ipv6EchoReplyPacket;
use icmpv6_echo::echo_request::MutableEchoRequestPacket as MutableIpv6EchoRequestPacket;

type Seq = u16;

enum OptTtl {  // sames as Option<u8>, but can implement Display
    None,
    Some(u8)
}

struct PingResponse {
    nbytes : usize,
    addr : IpAddr,
    seq : Seq,
    ttl : OptTtl,
    time : Instant,
}

impl std::fmt::Display for OptTtl {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            OptTtl::None => write!(f, "  -"),
            OptTtl::Some(ttl) => write!(f, "{}", ttl)
        }
    }
}

fn process_responses(mut rx : TransportReceiver,
                sender : &mpsc::Sender<PingResponse>) -> ! {
    let mut iter = ipv4_packet_iter(&mut rx);
    loop {
        let res = iter.next();
        let t = Instant::now();
        match res {
            Err (e) => {
                println!("Error receiving packet: {}", e);
            },
            Ok ((ipv4, addr)) => {
                if let Some (echoreply) = EchoReplyPacket::new(ipv4.payload()) {
                    if echoreply.get_icmp_type() == IcmpTypes::EchoReply &&
                        echoreply.get_identifier() == unsafe{getpid() as u16}
                    {
                        // XXX: check addr
                        let resp = PingResponse {
                            nbytes : ipv4.payload().len(),
                            addr : addr,
                            seq : echoreply.get_sequence_number(),
                            ttl : OptTtl::Some(ipv4.get_ttl()),
                            time : t,
                        };
                        if sender.send(resp).is_err() {
                            println!("Internal error: cannot send message to thread")
                        }
                    }
                }
            }
        }
    }
}

fn process_responses_v6(mut rx : TransportReceiver,
                sender : &mpsc::Sender<PingResponse>) -> ! {
    let mut iter = icmpv6_packet_iter(&mut rx);
    loop {
        let res = iter.next();
        let t = Instant::now();
        match res {
            Err (e) => {
                println!("Error receiving packet: {}", e);
            },
            Ok ((icmpv6, addr)) => {
                if let Some (echoreply) = Ipv6EchoReplyPacket::new(icmpv6.packet()) {
                    if echoreply.get_icmp_type() == Icmpv6Types::EchoReply &&
                        echoreply.get_identifier() == unsafe{getpid() as u16}
                    {
                        // XXX: check addr
                        let resp = PingResponse {
                            nbytes : echoreply.payload().len(),
                            addr : addr,
                            seq : echoreply.get_sequence_number(),
                            // TODO we can't extract it, since we're operating below the IPv6 headers, should probably rewrite everything using IPv6 packets (too bored for that right now)
                            ttl : OptTtl::None,
                            time : t,
                        };
                        if sender.send(resp).is_err() {
                            println!("Internal error: cannot send message to thread")
                        }
                    }
                }
            }
        }
    }
}

fn icmp_populate_packet(ipv4 : &mut MutableIpv4Packet, icmp_payload : &[u8]) {
    let mut echo_req = MutableEchoRequestPacket::new(ipv4.payload_mut()).unwrap();
    echo_req.set_icmp_type(IcmpTypes::EchoRequest);
    echo_req.set_icmp_code(IcmpCode::new(0));
    let pid = unsafe {getpid()};
    echo_req.set_identifier(pid as u16);
    echo_req.set_sequence_number(88);
    echo_req.set_payload(icmp_payload);
}

fn icmp_calc_checksum(ipv4 : &MutableIpv4Packet) -> u16be {
    let icmp = IcmpPacket::new(ipv4.payload()).unwrap();
    icmp::checksum(&icmp)
}

fn icmp_checksum(ipv4 : &mut MutableIpv4Packet) {
    let csum = icmp_calc_checksum(ipv4);
    let mut ipv4_payload = ipv4.payload_mut();
    let mut echo_req = MutableEchoRequestPacket::new(ipv4_payload).unwrap();
    echo_req.set_checksum(csum);
}

fn echo_checksum_v6(echo : &mut MutableIpv6EchoRequestPacket, src: &Ipv6Addr, dest: &Ipv6Addr) {
    let csum = {
        let icmp = Icmpv6Packet::new(echo.packet()).unwrap();
        icmpv6::checksum(&icmp, *src, *dest)
        };
    echo.set_checksum(csum);
}

fn icmp_update_seq(ipv4 : &mut MutableIpv4Packet, seq : u16) {
    let mut echo_req = MutableEchoRequestPacket::new(ipv4.payload_mut()).unwrap();
    echo_req.set_sequence_number(seq)
}

fn icmp_set_timestamp(ipv4 : &mut MutableIpv4Packet) {
    let mut echo_req = MutableEchoRequestPacket::new(ipv4.payload_mut()).unwrap();
    let time = Local::now();
    let secs = time.timestamp();
    let ns = time.timestamp_subsec_nanos().to_be();
    // XXX: subtract start time
    let secs = (secs as u32).to_be();
    (&mut echo_req.payload_mut()[0..4]).write_u32::<BigEndian>(secs).unwrap();
    (&mut echo_req.payload_mut()[4..8]).write_u32::<BigEndian>(ns).unwrap();
}

fn populate_packet(pkt_buf : &mut [u8], dst : &Ipv4Addr, icmp_payload : &[u8]) {
    let buf_len = pkt_buf.len();
    let mut ipv4 = MutableIpv4Packet::new(pkt_buf).unwrap();

    ipv4.set_next_level_protocol(IpNextHeaderProtocols::Icmp);

    let ipv4_header_len = match MutableIpv4Packet::minimum_packet_size().checked_div(4) {
        Some (l) => l as u8,
        None => panic!("Invalid header len")
    };

    ipv4.set_header_length(ipv4_header_len);
    ipv4.set_total_length(buf_len as u16);
    ipv4.set_version(4);
    ipv4.set_ttl(64);
    ipv4.set_destination(*dst);
    ipv4.set_flags(Ipv4Flags::DontFragment);
    ipv4.set_options(&[]);
    icmp_populate_packet(&mut ipv4, icmp_payload);
}

fn send_ping (mut tx : TransportSender, dst : Ipv4Addr, len : usize) -> Box<FnMut(u16) -> ()> {

    let timestamp_size = 2 * mem::size_of::<u32>();
    let seq = (0u8..).take(u8::max_value() as usize).chain(Some(u8::max_value()));
    // Send the same payload as iputils-ping
    let icmp_payload : Vec<u8> = if len >= timestamp_size {
        (vec![0u8; timestamp_size].into_iter()).chain(seq.cycle()).take(len).collect()
    } else {
        // Not enough space for a timestamp
        seq.cycle().take(len).collect()
    };
    let icmp_len = MutableEchoRequestPacket::minimum_packet_size() +
        icmp_payload.len();
    let total_len = MutableIpv4Packet::minimum_packet_size() + icmp_len;

    let mut pkt_buf : Vec<u8> = vec!(0; total_len);

    populate_packet(&mut pkt_buf, &dst, &icmp_payload);
    Box::new(move |seq| {
        let mut ipv4 = MutableIpv4Packet::new(&mut pkt_buf).unwrap();
        icmp_update_seq(&mut ipv4, seq);
        if len >= timestamp_size {
            // This is totally unused, as we record the send time
            // ourselves. It's only here so our packets look similar
            // to iputils-ping. Perhaps we should replace it with a
            // cookie to get rid of identifier conflicts (the PID is
            // truncated to 16 bits, so we /could/ get confused with
            // some other ping running on the same host).
            icmp_set_timestamp(&mut ipv4)
        }
        icmp_checksum(&mut ipv4);

        match tx.send_to(ipv4, IpAddr::V4(dst)) {
            Ok (bytes) => if bytes != total_len { panic!("Short send count: {}", bytes) },
            Err (e) => panic!("Could not send: {}", e),
        }
    })
}

fn icmpv6_packet<'a>(pkt_buf: &'a mut [u8], icmp_payload: &[u8], seq: u16)
                     -> MutableIpv6EchoRequestPacket<'a> {
    let mut echo_req = MutableIpv6EchoRequestPacket::new(pkt_buf).unwrap();
    echo_req.set_icmp_type(Icmpv6Types::EchoRequest);
    echo_req.set_icmp_code(Icmpv6Code::new(0));
    let pid = unsafe {getpid()};
    echo_req.set_identifier(pid as u16);
    echo_req.set_sequence_number(seq);
    echo_req.set_payload(icmp_payload);
    echo_req
}

fn echo_set_timestamp_v6(echo : &mut MutableIpv6EchoRequestPacket) {
    let time = Local::now();
    let secs = time.timestamp();
    let ns = time.timestamp_subsec_nanos().to_be();
    // XXX: subtract start time
    let secs = (secs as u32).to_be();
    let payload = echo.payload_mut();
    (&mut payload[0..4]).write_u32::<BigEndian>(secs).unwrap();
    (&mut payload[4..8]).write_u32::<BigEndian>(ns).unwrap();
}

fn send_ping_v6(mut tx : TransportSender, src: Ipv6Addr, dst : Ipv6Addr, len : usize) -> Box<FnMut(u16) -> ()> {

    let timestamp_size = 2 * mem::size_of::<u32>();
    let seq = (0u8..).take(u8::max_value() as usize).chain(Some(u8::max_value()));
    // Send the same payload as iputils-ping
    let icmp_payload : Vec<u8> = if len >= timestamp_size {
        (vec![0u8; timestamp_size].into_iter()).chain(seq.cycle()).take(len).collect()
    } else {
        // Not enough space for a timestamp
        seq.cycle().take(len).collect()
    };
    let ip_len = MutableIpv6EchoRequestPacket::minimum_packet_size() +
        icmp_payload.len();
    let mut pkt_buf : Vec<u8> = vec!(0; ip_len);

    Box::new(move |seq| {
        let mut icmp = icmpv6_packet(&mut pkt_buf, &icmp_payload, seq);

        if len >= timestamp_size {
            // This is totally unused, as we record the send time
            // ourselves. It's only here so our packets look similar
            // to iputils-ping. Perhaps we should replace it with a
            // cookie to get rid of identifier conflicts (the PID is
            // truncated to 16 bits, so we /could/ get confused with
            // some other ping running on the same host).
            echo_set_timestamp_v6(&mut icmp)
        }
        // apparently, something lower level (Rust lib or kernel) in my Linux development
        // platform fixes the checksum anyway,
        // but I can't be sure other contexts behave the same way, so better do it.
        echo_checksum_v6(&mut icmp, &src, &dst);
        match tx.send_to(icmp, IpAddr::V6(dst)) {
            Ok (bytes) => if bytes != ip_len { panic!("Short send count: {} instead of {}", bytes, ip_len) },
            Err (e) => panic!("Could not send: {}", e),
        }
    })
}

const INITIAL_SEQ_NR : u64 = 1;

#[derive(Debug)]
struct Probe {
    seq : Seq,
    sent : Instant,
    received : Option<Instant>,
}

impl Probe {
    fn new(seq : Seq, t : Instant) -> Self{
        Probe {
            seq : seq,
            sent : t,
            received : None
        }
    }
    fn received(&mut self, t : Instant) {
        self.received =  Some(t)
    }
    fn rtt(&self) -> Option<Duration> {
        self.received.map(|rx| rx.duration_since(self.sent))
    }
}

#[derive(Debug)]
struct Stats {
    // Window size; can't be too large because we can't (in the general case)
    // have more than 2**16 packets in flight (size of the echoreq seq). Not
    // that is a concern in practice.
    n : u16,

    // Responses to our probes may arrive out of order. But the
    // exponantiated weighted moving average (EWMA) needs to be
    // computed in order. For this reason, we keep around the last
    // Self.n sent probes, so we can go back and recalculate the
    // packet loss EWMA when a probe in the window is responded to
    // (i.e. the packet changes from 'lost' or 'unknown' to 'responded
    // to'. The status of probes that slide out of the window is
    // frozen and added to the packet_loss accumulator.
    ring : VecDeque <Probe>,

    // This field records the packet loss EWMA for the probes that
    // have slid outside our window.
    packet_loss : Option<Ewma>,
}

impl Stats {
    // The 1.0 value for calculating the packet loss
    fn pl_unit() -> u64 {
        1000_000_000
    }
    fn new(n : u16) -> Result<Self, &'static str> {
        if n == 0 {
            Err("Cannot work with an empty window")
        } else {
            Ok(Stats {
                n : n,
                ring : VecDeque::with_capacity(n as usize),
                packet_loss : None,
            })
        }
    }
    fn probe(&mut self, seq : Seq, t : Instant) {
        if self.ring.len() == (self.n as usize) {
            let p = self.ring.pop_front().expect("Error popping from non-empty window");
            // Probe slides out of the window, the received/lost
            // designation needs to become final now (if we receive
            // a response to its seq later, there's no way to tell
            // if it's a dup or not, nor can we update the EWMA).
            let lost = match p.received {
                None => Self::pl_unit(),
                Some (_) => 0,
            };
            match self.packet_loss {
                Some (ref mut pl) => {
                    pl.add_sample(lost)
                },
                None => {
                    // This is the first packet that slides out the window
                    assert_eq!(p.seq, INITIAL_SEQ_NR as Seq);
                    self.packet_loss = Some(Ewma::new(lost))
                }
            }
        }
        self.ring.push_back(Probe::new(seq, t))
    }
    fn response(&mut self, seq : Seq, t : Instant) {
        match self.ring.iter_mut().find(|p| p.seq == seq) {
            None =>
            // XXX: here we want to be estimating the RTT time for that packet;
            // if the latency went up, the window for the moving average might
            // have become inadequate
                writeln!(&mut std::io::stderr(),
                         "Received seq {} outside the window", seq).unwrap(),
            Some (probe) => probe.received(t)
        }
    }
    fn last_probe_pending(&self) -> bool {
        self.ring.iter().last().iter().any(|p| p.received.is_none())
    }
    fn probe_by_seq(&self, seq : Seq) -> Option<&Probe> {
        self.ring.iter().find(|p| p.seq == seq)
    }
    fn estimate_packet_loss(&self, rtt : &Ewma) -> (f64, f64) {
        let now = Instant::now();
        let unit = Self::pl_unit();
        let mut iter = self.ring.iter().filter_map(|p| {
            match p.received {
                Some (_) =>
                    Some(0),
                None => {
                    let elapsed = Ns::from_duration(now.duration_since(p.sent));
                    if elapsed.0 > rtt.smoothed + 2 * rtt.variation {
                        // We consider this lost for the current calculation. If
                        // it does arrive later, we'll revise the packet loss percentage
                        // downwards.
                        Some(unit)
                    } else {
                        // Response pending, but reasonably so. Exclude this
                        // probe from the packet loss calculation.
                        None
                    }
                }
            }});
        let mut pl = match self.packet_loss {
            Some (ref pl) => pl.clone(),
            None => {
                // All sent probes are still recorded in the window
                Ewma::new(iter.next().unwrap())
            }
        };
        for s in iter {
            pl.add_sample(s)
        };
        (pl.smoothed as f64 / unit as f64, pl.variation as f64 / unit as f64)
    }
}

#[derive(PartialEq, PartialOrd, Eq, Ord)]
struct Ns(u64);

impl fmt::Display for Ns {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let ns = self.0;
        for (i, unit) in ["s", "ms", "us"].into_iter().enumerate() {
            let exp = 9 - i * 3;
            let conv = pow::<u64>(10, exp);
            let res = ns / conv;
            if res != 0 {
                return f.pad(&format!("{} {}", res, unit))
            }
        }
        f.pad(&format!("{} ns", ns))
    }
}


impl Sub for Ns {
    type Output = Ns;
    fn sub(self, other: Ns) -> Ns{
        Ns(self.0 - other.0)
    }
}

#[test]
fn test_nanoseconds_display() {
    assert_eq!(format!("{}", Ns(0)), "0 ns");
    assert_eq!(format!("{}", Ns(10)), "10 ns");
    assert_eq!(format!("{}", Ns(1000)), "1 us");
    assert_eq!(format!("{}", Ns(10_000)), "10 us");
    assert_eq!(format!("{}", Ns(10_000_000)), "10 ms");
    assert_eq!(format!("{}", Ns(10_000_000_000)), "10 s");
    assert_eq!(format!("{}", Ns(10_000_000_000_000)), "10000 s");
}

impl Ns {
    fn from_duration(d : Duration) -> Self {
        Ns(d.as_secs() * 1000_000_000 + (d.subsec_nanos() as u64))
    }

    fn to_duration(&self) -> Duration {
        let ns = self.0;
        let secs = ns / 1_000_000_000;
        let nanos = (ns % 1_000_000_000) as u32;
        Duration::new(secs, nanos)
    }
}

struct Percent(f64);

impl fmt::Display for Percent {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.pad(&format!("{:.0}%", self.0))
    }
}

struct IpAddrPaddable (IpAddr);

// IpAddr's Display implementation doesn't respect the padding flags, we
// need to wrap it for Columnar to Just Work with it.
impl fmt::Display for IpAddrPaddable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.0 {
            IpAddr::V4 (v4) => f.pad(&format!("{}", v4)),
            IpAddr::V6 (v6) => f.pad(&format!("{}", v6)),
        }
    }
}

fn do_probe(probe : &mut Box<FnMut(u16) -> ()>, stats: &mut Stats,
            seq : Seq) -> Instant {
    let probe_time = Instant::now();
    probe(seq);
    stats.probe(seq, probe_time);
    probe_time
}

// Update our statistics and return the RTT of the response
fn do_response(rtt_estimate : &mut Option<Ewma>,
               stats : &mut Stats, resp : &PingResponse)
               -> Option<Ns> {
    stats.response(resp.seq, resp.time);
    match stats.probe_by_seq(resp.seq) {
        None => None, // XXX: outside window
        Some (p) => {
            let rtt_sample = Ns::from_duration(p.rtt().unwrap());
            match *rtt_estimate {
                None =>
                    *rtt_estimate = Some (Ewma::new(rtt_sample.0)),
                Some (ref mut rtt) => {
                    rtt.add_sample(rtt_sample.0)
                },
            };
            Some (rtt_sample)
        }
    }
}

fn maybe_resolve(s : &str) -> Result<Vec<IpAddr>, String> {
    match IpAddr::from_str(s) {
        Ok (addr) => Ok (vec![addr]),
        Err (_) => {
            let addrs = try!(resolve_host(&s).map_err(|e| String::from(e.description())));
            Ok (addrs.collect())
        }
    }
}

fn select_destination_address(addrs: &[IpAddr]) -> Result<IpAddr, String> {
    let mut found: Option<IpAddr> = None;

    for addr in addrs {
        if addr.is_ipv6() || found.is_none() { found = Some(*addr); }
        if addr.is_ipv6() { break; }
    }

    match found {
        None => Err("Could not find a single address, how's that possible?".to_owned()),
        Some(addr) => Ok(addr)
    }
}

fn print_resolved_addrs(dest : &str, selected : &IpAddr, addrs: &[IpAddr]) {
    let mut addrstrs = addrs.iter().map(|a| format!("{}", a)).peekable();
    let mut acc = String::new();
    loop {
        match addrstrs.next() {
            Some (s) => acc.push_str(&s),
            None => break,
        };
        if addrstrs.peek().is_some() {
            acc.push_str(" ")
        }
    }
    writeln!(&mut std::io::stderr(),
             "PING {} for {} ({})", selected, dest, acc).unwrap();

}

fn columns_simple () -> Vec<Column> {
    vec![
        Column::new("Seq", 5, 2),
        Column::new("RTT", 9, 2),
        Column::new("smooth RTT", 10, 3),
        Column::new("RTT variation", 13, 3),
        Column::new("Packet loss", 11, 3),
    ]
}


fn columns_extended () -> Vec<Column> {
    vec![
        Column::new("Seq", 5, 2),
        Column::new("Bytes", 5, 2),
        Column::new("TTL", 5, 2),
        Column::new("From", 15, 2),
        Column::new("RTT", 9, 2),
        Column::new("smooth RTT", 10, 3),
        Column::new("RTT variation", 13, 3),
        Column::new("Packet loss", 11, 3),
    ]
}

fn to_display<T : fmt::Display>(v : Option<&T>) -> Option<&fmt::Display> {
    v.map (|v| v as &fmt::Display)
}

fn output_row<'a> (opt_extended_format : bool, columnar : &Columnar,
                   stats : &Stats, resp : Option<&'a PingResponse>,
                   rtt_sample : &Option<Ns>,
                   rtt : Option<&Ewma>) {
    let seq = resp.map(|r| &r.seq as &fmt::Display);
    let nbytes = resp.map (|r| &r.nbytes as &fmt::Display);
    let ttl = resp.map(|r| &r.ttl as &fmt::Display);
    let addr = resp.map(|r| (IpAddrPaddable(r.addr)));
    let rtt_smoothed = rtt.map(|rtt| Ns(rtt.smoothed));
    let rtt_variation = rtt.map(|rtt| Ns(rtt.variation));
    // Calculate the packet loss based on the RTT estimate. If we
    // don't have an RTT estimate, that means we haven't received a
    // a single response yet, so our packet loss has to be 100%
    let packet_loss = rtt.map(|rtt| stats.estimate_packet_loss(rtt)).map( |pl| {
        Percent(pl.0 * 100.0)}).unwrap_or(Percent(100.0));
    let values = match opt_extended_format {
        true => vec![
            seq,
            nbytes,
            ttl,
            to_display(addr.as_ref()),
            to_display(rtt_sample.as_ref()),
            to_display(rtt_smoothed.as_ref()),
            to_display(rtt_variation.as_ref()),
            Some (&packet_loss),
        ],
        false => vec![
            seq,
            to_display(rtt_sample.as_ref()),
            to_display(rtt_smoothed.as_ref()),
            to_display(rtt_variation.as_ref()),
            Some (&packet_loss),
        ],
    };
    println!("{}", columnar.format(values));
}

fn passive_update(opt_extended_format : bool, rtt : &Option<Ewma>,
                  columnar : &Columnar, stats : &Stats) {
    output_row(opt_extended_format, columnar, stats, None, &None, rtt.as_ref())
}

fn parse_cli_int<T : FromStr<Err=ParseIntError>>(s : &str) -> T {
    match T::from_str(s) {
        Ok (x) => x,
        Err (err) => {
            writeln!(&mut std::io::stderr(),
                     "Could not parse '{}' as an integer: {}", s, err).unwrap();
            std::process::exit(2)
        }
    }
}

fn parse_cli_float(s : &str) -> f64 {
    match f64::from_str(s) {
        Ok (x) => x,
        Err (err) => {
            writeln!(&mut std::io::stderr(),
                     "Could not parse '{}' as a floating point number: {}",
                     s, err).unwrap();
            std::process::exit(2)
        }
    }
}

fn main() {
    let mut dest : Option<String> = None;
    let mut opt_interval : Option<String> = None;
    let mut opt_window_size : Option<String> = None;
    let mut opt_extended_format : bool = false;
    let mut opt_send_size :Option<String> = None;
    {
        let mut parser = ArgumentParser::new();
        parser.refer(&mut dest).add_argument("address", StoreOption,
                                             "Target hostname or IPv4 address");
        parser.refer(&mut opt_interval).add_option(&["-i"], StoreOption, "Send interval");
        parser.refer(&mut opt_send_size).add_option(&["-s", "--packet-size"], StoreOption,
                                               "Payload size in bytes");
        parser.refer(&mut opt_window_size).
            add_option(&["--window"],StoreOption,
                       "Adaptive packet loss calculation for the last N probes");
        parser.refer(&mut opt_extended_format).
            add_option(&["-x", "--extended"], StoreTrue,
                       "Include additional information in the output");
        match parser.parse_args() {
            Ok (()) => (),
            Err (e) => {
                writeln!(&mut std::io::stderr(), "Error parsing arguments: {}", e).unwrap();
                std::process::exit(2)
            }
        }
    }
    let columns = match opt_extended_format {
        false => columns_simple (),
        true => columns_extended (),
    };
    let columnar = columns.into_iter().
        fold(Columnar::new(), |columnar, col| columnar.push_col(col));

    let send_size = match opt_send_size {
        None => 56,
        Some (s) => parse_cli_int(&s),
    };
    let interval = match opt_interval {
        None => 1000_000_000,
        Some (s) => (parse_cli_float(&s) * 1000_000_000.0) as u64
    };
    let window_size = match opt_window_size {
        None => {
            // It takes a bit over 15 samples after a single packet loss,
            // for the packet loss percentage to drop to below 1%. Default
            // a lange enough value so that there are no abrupt changes in
            // the packet loss percentage when a packet loss event slides
            // outside our window. We still want a window so that the packet
            // loss can go down to zero eventually (though perhaps the .1
            // f64 precision is too much and we can just switch to .0
            // and drop the window logic).
            20 as u16
        },
        Some (sz) => parse_cli_int(&sz),
    };

    let dest = dest.unwrap_or_else(|| {
        writeln!(&mut std::io::stderr(),
                 "Need to supply a destination host").unwrap();
        std::process::exit(2)
    });
    let dst = match maybe_resolve(&dest) {
        Err (e) => {
            writeln!(&mut std::io::stderr(),
                     "Name resolution error: {}", e).unwrap();
            std::process::exit(1)
        },
        Ok (addrs) => {
            match select_destination_address(&addrs) {
                Ok(addr) => {
                    print_resolved_addrs(&dest, &addr, &addrs);
                    addr
                },
                Err(msg) => {
                    writeln!(&mut std::io::stderr(), "{}", &msg).unwrap();
                    std::process::exit(1)
                }
            }
        },
    };

    let channel_type = match dst {
        IpAddr::V4(_) => Layer3(IpNextHeaderProtocols::Icmp),
        IpAddr::V6(_) => Layer4(TransportProtocol::Ipv6(IpNextHeaderProtocols::Icmpv6))
    };
    let (tx, rx) = match transport_channel(4096, channel_type) {
        Ok ((tx, rx)) => (tx, rx),
        Err (e) => panic!("Could not create the transport channel: {}", e)
    };

    let src6 = Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 1);
    let mut probe = match dst {
        IpAddr::V4(addr) => send_ping(tx, addr, send_size),
        IpAddr::V6(addr) => send_ping_v6(tx, src6, addr, send_size)
    };
    let mut seq = INITIAL_SEQ_NR;
    let mut stats = Stats::new(window_size).expect("Couldn't create ring buffer");
    let mut rtt_estimate : Option<Ewma> = None;

    // Unfortunately, pnet currently only offers a blocking interface, so we
    // have to use a helper thread in order to wait for the next packet OR
    // the expiration of the send timer.
    let (sender, receiver) = mpsc::channel();
    let process_fn = match dst {
        IpAddr::V4(_) => process_responses,
        IpAddr::V6(_) => process_responses_v6
    };
    thread::spawn(move || {process_fn(rx, &sender)});
    let start_time = Instant::now();

    println!("{}", columnar.header());

    loop {
        let time_elapsed = Instant::now().duration_since(start_time);
        // Once (seq_nr - 1) * send_interval nanoseconds have passed
        // from our starting time, we need to send the next probe. We
        // have to calculate the next send time based on our start time,
        // otherwise we'd accumulate significant drift for long-lasting
        // executions (the sleep interval is always >= than the interval
        // we requested).
        let ns_offset_of_next_send =
            Ns(interval.checked_mul((seq - INITIAL_SEQ_NR) as u64).unwrap());

        if Ns::from_duration(time_elapsed) > ns_offset_of_next_send {
            if stats.last_probe_pending() {
                // Don't go too long without printing statistics
                passive_update(opt_extended_format, &rtt_estimate, &columnar, &stats)
            }
            let _ = do_probe(&mut probe, &mut stats, seq as u16);
            seq = seq.checked_add(1).unwrap();
        } else {
            // It's not time to send yet.
            let diff = ns_offset_of_next_send - Ns::from_duration(time_elapsed);
            let timeo = diff.to_duration();
            match receiver.recv_timeout(timeo) {
                Ok (resp) => {
                    if let Some(sample) = do_response(&mut rtt_estimate, &mut stats, &resp) {
                        output_row(opt_extended_format, &columnar, &stats,
                                   Some (&resp), &Some (sample), rtt_estimate.as_ref())
                    }
                },
                Err (RecvTimeoutError::Timeout) => {
                    // Time to probe again
                },
                Err (RecvTimeoutError::Disconnected) => {
                    println!("Internal error: receiver thread exited");
                    std::process::exit(1)
                }
            }
        }
    }
}
