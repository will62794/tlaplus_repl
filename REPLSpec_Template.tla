------------------------- MODULE %s -------------------------
EXTENDS Naturals, Sequences, TLC
VARIABLE x
Init ==  x=0
ToPrint == %s
Next == /\ PrintT("TLAREPL_START")
		/\ PrintT(ToPrint)
		/\ PrintT("TLAREPL_END")
		/\ UNCHANGED x


=============================================================================
