---- MODULE BlockingQueue ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Producers, Consumers, BufCapacity

ASSUME Assumption == /\ Producers # {}
                     /\ Consumers # {}
                     /\ Producers \intersect Consumers = {}
                     /\ BufCapacity \in (Nat \ {0})

--------------------------------------------------------------------------------
VARIABLES buffer, waitSet
vars == <<buffer, waitSet>>

Notify == /\ IF waitSet # {}
             THEN \E x \in waitSet: waitSet' = waitSet \ {x}
             ELSE UNCHANGED waitSet

Wait(t) == /\ waitSet' = waitSet \union {t}
           /\ UNCHANGED <<buffer>>

--------------------------------------------------------------------------------
Put(t, d) == \/ /\ Len(buffer) < BufCapacity
                /\ buffer' = Append(buffer, d)
                /\ Notify
             \/ /\ Len(buffer) = BufCapacity
                /\ Wait(t) 

Get(t) == \/ /\ buffer # <<>>
                /\ buffer' = Tail(buffer)
                /\ Notify
          \/ /\ buffer = <<>>
             /\ Wait(t)

-------------------------------------------------------------------------------- 
Init == /\ buffer = <<>>
        /\ waitSet = {}

Next == \/ \E p \in (Producers \ waitSet): Put(p, p)
        \/ \E c \in (Consumers \ waitSet): Get(c)

TypeInv == /\ buffer \in Seq(Producers)
           /\ Len(buffer) \in 0..BufCapacity
           /\ waitSet \in SUBSET (Producers \union Consumers)

Invariant == waitSet # (Producers \cup Consumers)

====