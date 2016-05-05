// Josh Blome and Joe Carroll
// RDT 2.0

// Assumptions
//	One sender, one receiver
//	

module RDT20

open util/ordering[NetworkState]

sig Data {}
abstract sig Checksum {}
one sig GoodChecksum extends Checksum{}
one sig BadChecksum extends Checksum{}

abstract sig SenderState{}
one sig WaitCall extends SenderState{}
one sig WaitResponse extends SenderState{}

abstract sig Packet {
	checksum: one Checksum
}

sig DataPacket extends Packet{
	data: one Data
}
one sig Ack extends Packet {}
one sig Nack extends Packet {}

fact {no d:Data | #d.~data != 1}

sig NetworkState {
	sendBuffer: set Data,
	receiveBuffer: set Data,
	channel: lone Packet,
	senderState: one SenderState,
	sentData: lone Data
}

fun Data.toPacket : Packet {
	this.~data
}

fun Packet.toData : Data {
	this.data
}

fun Data.generateChecksum : Checksum {
	GoodChecksum + BadChecksum
}

pred Init [s: NetworkState] {
	s.channel = Ack
	no s.receiveBuffer
	s.sendBuffer = Data
	s.senderState = WaitCall
	no s.sentData
}

pred End [s: NetworkState] {
	no s.channel
	no s.sendBuffer
	s.receiveBuffer = Data
	no s.sentData
}

pred Step [s1, s2: NetworkState]  {
	(s1.senderState = WaitCall and
		s2.senderState = WaitResponse and
		s1.receiveBuffer = s2.receiveBuffer and
			((s1.channel = Ack and 
				s2.sendBuffer = s1.sendBuffer - s1.sentData and
				(one d: s2.sendBuffer |
					s2.channel  = d.toPacket and
					s2.sentData = d) or
				End[s2])
			or
			(s1.channel = Nack and 
				s2.channel = s1.sentData.toPacket and
				s1.sentData = s2.sentData and
				s2.sendBuffer = s1.sendBuffer))
	)
	or
	(s1.senderState = WaitResponse and
		s2.senderState = WaitCall and
		s1.sendBuffer = s2.sendBuffer and
		s1.sentData = s2.sentData and
		((s1.channel.checksum = GoodChecksum and
			s2.receiveBuffer = s1.receiveBuffer + s1.channel.data and
			s2.channel = Ack)
		or
		(s1.channel.checksum = BadChecksum and
			s2.receiveBuffer = s1.receiveBuffer and
			s2.channel = Nack)))
	or
	(End[s1] and End[s2])
}

pred Trace {
	Init[first]
	all s: NetworkState - last |
		let s' = s.next |
			Step[s, s']
}

pred CanPass {
	Trace and
	some s:NetworkState | End[s]
}

assert MustPass {
	Trace=>End[last]
}

pred Show {}

run Show for 3

run Init for 3 but 3 Packet

run Trace for 7 but exactly 3 Packet

run CanPass for 8 but exactly 3 DataPacket

check MustPass for 15 but 3 Packet
