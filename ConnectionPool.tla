---- MODULE ConnectionPool ----
EXTENDS Naturals, Sequences
CONSTANTS PoolSize, MaxPoolSize
VARIABLE pool

Node == [idle: BOOLEAN]

TypeOk ==
    /\ pool \in Seq(Node)

-------------------------

RemoveAt(seq, i) ==
    [j \in 1..(Len(seq)-1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

Open ==
    /\ Len(pool) < MaxPoolSize
    /\ pool' = Append(pool, [idle |-> TRUE])

Close ==
    /\ Len(pool) > PoolSize
    /\ \E i \in 1..Len(pool) :
        /\ pool[i].idle = TRUE
        /\ pool' = RemoveAt(pool, i)

Borrow ==
    /\ \E i \in 1..Len(pool) :
        /\ pool[i].idle = TRUE
        /\ pool' = [pool EXCEPT ![i].idle = FALSE]

Return ==
    /\ \E i \in 1..Len(pool) :
        /\ pool[i].idle = FALSE
        /\ pool' = [pool EXCEPT ![i].idle = TRUE]

-------------------------
Init == pool = [i \in 1..PoolSize |-> [idle |-> TRUE]]

Next == Open \/ Close \/ Borrow \/ Return

Spec == Init /\ [][Next]_pool
====
