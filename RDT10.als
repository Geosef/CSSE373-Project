// Josh Blome and Joe Carroll
// RDT 1.0

// Assumptions
//	One sender, one receiver
//	

module RDT10

open util/ordering[NetworkState]

sig Data {}
sig Checksum {}

sig Packet {
	data: one Data,
	checksum: one Checksum
}

fact {no d:Data | #d.~data != 1}

sig NetworkState {
	sendBuffer: set Data,
	receiveBuffer: set Data,
	channel: lone Packet
}

fun Data.toPacket : Packet {
	this.~data
}

fun Packet.toData : Data {
	this.data
}

pred Init [s: NetworkState] {
	no s.channel
	no s.receiveBuffer
	s.sendBuffer = Data
}

pred End [s: NetworkState] {
	no s.channel
	no s.sendBuffer
	s.receiveBuffer = Data
}

pred Step [s1, s2: NetworkState]  {
	// Some new data has been sent
	(one d: s1.sendBuffer |
		s2.sendBuffer = s1.sendBuffer - d and
		s2.channel = d.toPacket and
		no s1.channel and
		s1.receiveBuffer = s2.receiveBuffer)
	or
	// Some new data has been received
	(one d: s2.receiveBuffer |
		s2.receiveBuffer = s1.receiveBuffer + d and
		s1.channel = d.toPacket and
		no s2.channel and
		s1.sendBuffer = s2.sendBuffer)
}

pred Trace {
	Init[first]
	all s: NetworkState - last |
		let s' = s.next |
			Step[s, s'] or End[s]
}

pred Show {}

run Show for 3

run Init for 3 but 3 Packet

run Trace for 7 but exactly 3 Packet, exactly 3 Data
