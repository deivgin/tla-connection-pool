---- MODULE ConnectionPool ----
EXTENDS Naturals, Sequences
CONSTANTS PoolSize, MaxPoolSize
VARIABLE pool, nextId
vars == <<pool, nextId>>

Node == [id: Nat, idle: BOOLEAN]

TypeOk ==
    /\ pool \in Seq(Node)
    /\ nextId \in Nat

Init ==
    /\ pool = [i \in 1..PoolSize |-> [id |-> i, idle |-> TRUE]]
    /\ nextId = PoolSize + 1

-------------------------

Open ==
    /\ Len(pool) < MaxPoolSize
    /\ \A i \in 1..Len(pool) : ~pool[i].idle
    /\ pool' = Append(pool, [id |-> nextId, idle |-> TRUE])
    /\ nextId' = nextId + 1

Borrow ==
    /\ \E i \in 1..Len(pool) :
        /\ pool[i].idle = TRUE
        /\ pool' = [pool EXCEPT ![i].idle = FALSE]
        /\ UNCHANGED nextId

Return ==
    /\ \E i \in 1..Len(pool) :
        /\ pool[i].idle = FALSE
        /\ pool' = [pool EXCEPT ![i].idle = TRUE]
        /\ UNCHANGED nextId

-------------------------

Next == Open \/ Borrow \/ Return

Spec == Init /\ [][Next]_vars

-------------------------

PoolSizeBounds == Len(pool) <= MaxPoolSize

UniqueIds == \A i, j \in 1..Len(pool) : i # j => pool[i].id # pool[j].id

====
