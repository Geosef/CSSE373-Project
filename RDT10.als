// Josh Blome and Joe Carroll
// RDT 1.0

// Assumptions
//	One sender, one receiver
//	

module RDT10

open util/ordering[State]

abstract sig Port {
	data: set Data
}

sig Sender extends Port {

}

sig Receiver extends Port {

}

sig Data {

} {no Data - Sender.data}

sig State {
	sender: Sender,
	receiver: Receiver
}

pred Init [s: State] {
	no s.receiver.data
	no s.sender.data
}

pred End [s: State] {
	s.sender.data = Data
	s.receiver.data = Data
}

pred Step [s1, s2: State]  {
	// Some new data has been sent
	(some d: s2.sender.data |
		s2.sender.data = s1.sender.data + d and
		s1.sender.data = s2.sender.data - d and
		s1.receiver.data = s2.receiver.data)
	or
	// Some new data has been received
	(some d: s1.sender.data |
		s2.receiver.data = s1.receiver.data + d and
		s1.receiver.data = s2.receiver.data - d and
		s1.sender.data = s2.sender.data)
}

pred Trace {
	Init[first]
	all s: State - last |
		let s' = s.next |
			Step[s, s'] or End[s]
}

pred Show {}

run Show for 3

run Init for 3

run Trace for 8 but exactly 3 Data
