variable (p q : Prop)

-- Proving P implies P - the way to do this is writing a function that returns its input (the identity)
example : p -> p := fun h => h

-- Proving P^Q given P and Q - construct a function that takes in h and r and returns h /\ r
example : p -> q -> p /\ q := fun h => fun r => ⟨h, r⟩
-- OR with shorthand notation
example : p -> q -> p /\ q := fun h r => ⟨h, r⟩

-- Proving Q^P given P^Q - same as above but we have a destruction step
example: p /\ q -> q /\ p := fun ⟨h, r⟩ => ⟨r, h⟩

-- Proving P implies (P OR Q)
example : p -> p \/ q := fun h => Or.inl h
example : q -> p \/ q := fun h => Or.inr h

-- Proving (P OR Q) implies (Q OR P)
example : p \/ q -> q \/ p :=
    fun h => match h with
        | Or.inl hp => Or.inr hp -- p -> q \/ p
        | Or.inr hq => Or.inl hq -- q -> q \/ p
