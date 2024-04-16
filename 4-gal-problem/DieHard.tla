---- MODULE DieHard ----
EXTENDS TLC, Integers

VARIABLES small, big

TypeOK == /\ small \in 0..3
          /\ big   \in 0..5

HeroNotOK == big # 4

FillSmall == /\ small' = 3
             /\ big'   = big

FillBig == /\ big'   = 5
           /\ small' = small

EmptySmall == /\ small' = 0
              /\ big'   = big

EmptyBig == /\ big'   = 0
            /\ small' = small
 
SmallToBig == IF big + small <= 5
              THEN /\ big' = big + small
                   /\ small' = 0
              ELSE /\ big' = 5
                   /\ small' = big + small - 5

BigToSmall == IF big + small <= 3
              THEN /\ small' = big + small
                   /\ big' = 0
              ELSE /\ small' = 3
                   /\ big' = big + small - 3

Init == /\ small = 0
        /\ big = 0

Next == \/ FillSmall
        \/ FillBig
        \/ EmptySmall
        \/ EmptyBig
        \/ SmallToBig
        \/ BigToSmall
====