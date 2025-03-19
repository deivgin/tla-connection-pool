---- MODULE ConnectionPool ----
EXTENDS Naturals, Sequences
CONSTANTS PoolSize, MaxPoolSize, Timeout
VARIABLE pool, nextId, time
vars == <<pool, nextId, time>>

Node == [id: Nat, idle: BOOLEAN, timeout: Nat]

TypeOk ==
    /\ Timeout \in Nat
    /\ pool \in Seq(Node)
    /\ nextId \in Nat
    /\ time \in 1..Timeout

Init ==
    /\ pool = [i \in 1..PoolSize |-> [id |-> i, idle |-> TRUE, timeout |-> 0]]
    /\ nextId = PoolSize + 1
    /\ time = 1

-------------------------

RemoveAtIndex(seq, idx) ==
    [i \in 1..(Len(seq) - 1) |->
        IF i < idx THEN seq[i] ELSE seq[i + 1]]

Open ==
    /\ Len(pool) < MaxPoolSize
    /\ \A i \in 1..Len(pool) : ~pool[i].idle
    /\ pool' = Append(pool, [id |-> nextId, idle |-> TRUE, timeout |-> 0])
    /\ nextId' = nextId + 1
    /\ UNCHANGED time

Close ==
    /\ Len(pool) > PoolSize
    /\ \A i \in 1..Len(pool) :
        /\ pool[i].idle
        /\ pool[i].timeout = Timeout
        /\ pool' = RemoveAtIndex(pool, i)

Borrow ==
    /\ \E i \in 1..Len(pool) :
        /\ pool[i].idle
        /\ pool' = [pool EXCEPT ![i].idle = FALSE]
        /\ UNCHANGED <<nextId, time>>

Return ==
    /\ \E i \in 1..Len(pool) :
        /\ ~pool[i].idle
        /\ pool' = [pool EXCEPT ![i].idle = TRUE]
        /\ UNCHANGED <<nextId, time>>

Tick ==
    /\ \A i \in 1..Len(pool) :
        /\ pool[i].idle
        /\ pool' = [pool EXCEPT ![i].timeout = time]
        /\ time' = time + 1
        /\ UNCHANGED nextId

-------------------------

Next == Open \/ Borrow \/ Return \/ Tick \/ Close

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-------------------------

PoolSizeBounds ==
    /\ Len(pool) >= PoolSize
    /\ Len(pool) <= MaxPoolSize

UniqueIds == \A i, j \in 1..Len(pool) : i # j => pool[i].id # pool[j].id

NodeTimeoutBounds == \A i \in 1..Len(pool) : pool[i].timeout <= Timeout

ActiveConnections == \A i \in 1..Len(pool) : ~pool[i].idle => pool[i].timeout = 0

EventualAvailability == []<>(\E i \in 1..Len(pool) : pool[i].idle)

====
