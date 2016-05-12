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
one sig Sending extends SenderState{}
one sig Waiting extends SenderState{}

abstract sig ReceiverState{}
one sig Receiving1 extends ReceiverState {}
one sig Receiving2 extends ReceiverState {}

abstract sig Packet {
}

sig DataPacket extends Packet{
	data: one Data,
	seqNum: one ReceiverState
}
one sig Ack extends Packet {}
one sig Nack extends Packet {}

fact {no d:Data | #d.~data != 1}

sig NetworkState {
	sendBuffer: set Data,
	receiveBuffer: set Data,
	channel: lone Packet,
	senderState: one SenderState,
	receiverState: one ReceiverState,
	sentData: lone Data,
	getChecksum: one Checksum
}

fun Data.toPacket : Packet {
	this.~data
}

fun Packet.toData : Data {
	this.data
}

pred Init [s: NetworkState] {
	s.channel = Ack
	no s.receiveBuffer
	s.sendBuffer = Data
	s.senderState = Sending
	no s.sentData
	s.receiverState = Receiving1
	s.getChecksum = GoodChecksum
}

pred End [s: NetworkState] {
	no s.channel
	no s.sendBuffer
	s.receiveBuffer = Data
	no s.sentData
}

pred ResendPacket [s1, s2: NetworkState] {
	s2.sendBuffer = s1.sendBuffer and
	s2.sentData = s1.sentData and
	s2.channel = s1.sentData.toPacket
}

pred SendNextPacket [s1, s2: NetworkState] {
	s2.sendBuffer = s1.sendBuffer - s1.sentData and
		((one d: s2.sendBuffer |
			s2.channel = d.toPacket and
			s2.sentData = d) or End[s2])
}

pred SendAck [s1, s2: NetworkState] {
	s2.receiveBuffer = s1.receiveBuffer + s1.channel.data and
	s2.channel = Ack and
	s2.receiverState != s1.receiverState
}

pred SendNack [s1, s2: NetworkState] {
	s2.receiveBuffer = s1.receiveBuffer and
	s2.channel = Nack and
	s2.receiverState = s1.receiverState
}

pred Step [s1, s2: NetworkState]  {
	(
		s1.senderState = Sending and
		s2.senderState = Waiting and
		s1.receiveBuffer = s2.receiveBuffer and
		s1.receiverState = s2.receiverState and
		(
			(
				s1.channel in Nack and ResendPacket[s1,s2]
			)
			or
			(
				s1.channel in Ack and 
				(
					(s1.getChecksum = GoodChecksum and SendNextPacket[s1, s2])
					or
					(s1.getChecksum = BadChecksum and ResendPacket[s1, s2] )
				)
			)
		)
	)
	or
	(
		s1.senderState = Waiting and
		s2.senderState = Sending and
		s1.sendBuffer = s2.sendBuffer and
		s1.sentData = s2.sentData and
		(
			(
				s1.channel.seqNum = s1.receiverState and
				(
					(s1.getChecksum = GoodChecksum and SendAck[s1, s2] ) or
					(s1.getChecksum = BadChecksum and SendNack[s1, s2] )
				)
			)
			or
			(
				s1.channel.seqNum != s1.receiverState and SendNack[s1, s2]
			)
		)
	)
	or
	(
		End[s1] and End[s2]
	)
}

pred Trace {
	Init[first]
	all s: NetworkState - last |
		let s' = s.next |
			Step[s, s']
}

pred OneError {
	all dp: DataPacket | #channel.dp = 2
	// The number of times the packet appears in the channel = 2 implies
	// It has been rejected exactly once
}

pred CanPass {
	Trace and (some s:NetworkState | End[s])
}

pred CanPassWith1Error {
	(Trace and OneError) and (some s: NetworkState | End[s])
}

assert MustPass {
	Trace implies (some s: NetworkState | End[s])
}

assert MustPassWith1Error {
	(Trace and OneError) implies (some s: NetworkState | End[s])
}

pred Show {}

run CanPass for 8 but exactly 3 DataPacket

run CanPassWith1Error for 14 but exactly 2 DataPacket

check MustPass for 14 but 3 DataPacket

check MustPassWith1Error for 14 but 3 DataPacket
