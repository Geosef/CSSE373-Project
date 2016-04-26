// Josh Blome and Joe Carroll
// RDT 1.0

// Assumptions
//	One sender, one receiver
//	

module RDT10

open util/ordering[State]

abstract sig Port {
	
}

one sig Sender extends Port {
	data: set Data
} {no Data - data}

one sig Receiver extends Port {

}

sig Data {

}

sig State {
	sent: set Data,
	received: set Data
}

pred Init [s: State] {
	no s.received
	no s.sent
}

pred End [s: State] {
	Sender.data = s.received
}

pred Step [s1, s2: State]  {
	// Some new data has been sent
	(some d: Sender.data |
		s2.sent = s1.sent + d and
		s1.sent = s2.sent - d)
	or
	// Some new data has been received
	(some d: s1.sent |
		s2.received = s2.received + d and
		s1.received = s2.received - d)
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

run Trace for 6 but exactly 3 Data
