---- MODULE HourClock ----
EXTENDS Integers, TLC

VARIABLE  hr

HCInit == hr \in (1..12)

HCNext == hr' = (hr % 12) + 1

HC == HCInit /\ [][HCNext]_hr

THEOREM HC => []HCInit
====