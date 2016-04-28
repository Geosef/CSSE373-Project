// Josh Blome and Joe Carroll
// RDT 1.0

// Assumptions
//	One sender, one receiver
//	

module RDT10

open util/ordering[NetworkState]

sig Data {
	checksum: one Checksum,
	packet: one Packet
}

sig Checksum {}
sig Packet {
	data: some Data
}

sig NetworkState {
	sendBuffer: set Data,
	receiveBuffer: set Data,
	channel: lone Packet
}

fun Data.packageData : Packet {
	this.packet
}

fun Packet.extractData : Data {
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
	one data: s1.sendBuffer |
		s1.sendBuffer = s2.sendBuffer - data
		s2.channel = data.packageData
		no s1.channel
		s1.receiveBuffer = s2.receiveBuffer
	or
	// Some new data has been received
	one data: s2.receiveBuffer |
		s1.receiveBuffer = s2.receiveBuffer - data
		s1.channel = data.packageData
		no s2.channel
		s1.sendBuffer = s2.sendBuffer
}

pred Trace {
	Init[first]
	all s: NetworkState - last |
		let s' = s.next |
			Step[s, s'] or End[s]
}

pred Show {}

run Show for 3

run Init for 3

run Trace for 8 but exactly 3 Data
