---- MODULE ConnectionPool ----
EXTENDS Naturals, Sequences
CONSTANTS PoolSize, MaxPoolSize
VARIABLE pool

Node == [idle: BOOLEAN]

TypeOk ==
    /\ pool \in Seq(Node)

-------------------------
Open ==
    /\ Len(pool) < MaxPoolSize
    /\ pool' = Append(pool, [idle |-> TRUE])

Close == TRUE

Borrow == TRUE

Return == TRUE

-------------------------
Init ==
    /\ pool = [i \in 1..PoolSize |-> [idle |-> TRUE]]

Next == Open

Spec == Init /\ [][Next]_pool
====
