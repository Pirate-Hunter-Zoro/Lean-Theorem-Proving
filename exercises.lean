variable (p q r: Prop)

-- Proving P → P - the way to do this is writing a function that returns its input (the identity)
example : p -> p := fun h => h

-- Proving P ∧ Q given P and given Q - construct a function that takes in h and r and returns h ∧ r
example : p -> q -> p /\ q := fun h => fun r => ⟨ h, r ⟩
-- OR with shorthand notation
example : p -> q -> p /\ q := fun h r => ⟨ h, r ⟩

-- Proving Q ∧ P given P ∧ Q - same as above but we have a destruction step
example: p /\ q -> q /\ p := fun ⟨ h, r ⟩ => ⟨ r, h ⟩

-- Proving P → (P ∨ Q)
example : p -> p \/ q := fun h => Or.inl h
example : q -> p \/ q := fun h => Or.inr h

-- Proving (P ∨ Q) → (Q ∨ P)
example : p \/ q -> q \/ p :=
    fun h => match h with
        | Or.inl hp => Or.inr hp -- p -> q \/ p
        | Or.inr hq => Or.inl hq -- q -> q \/ p

-- Proving ((P ∧ Q) → R) → (P → (Q → R)) - in English, once you have P, Q has "the power" to imply R
example: (p /\ q -> r) -> (p -> (q -> r)) := -- So define a function that takes in what we want - a function, and returns what we want - another function
    fun g => -- What we have - 'g' is a function that takes in hp of type p and hq of type q, and outputs f of type r
        fun hp => fun hq => g ⟨ hp, hq ⟩ -- What we want - this whole line is a function that takes in hp of type p and RETURNS a function that takes in hq of type q and returns hr of type r

-- Proving Transitivity - ((P → Q) ∧ (Q → R)) → (P → R)
example: ((p -> q) /\ (q -> r)) -> (p -> r) :=
    fun ⟨ hhp, hhq ⟩ => -- What are we given? A pairing of two functions hhp (which takes in hp of type p and returns hq of type q) and hhq (which takes in hq and returns hr of type r)
        fun hp => hhq (hhp hp) -- What we need - a function that takes in hp of type p and outputs hr of type r

-- Proving Contraposivity - (P → Q) ↔ (¬Q → ¬P) (WLOG, proving forward only implication is fine)
example: (p -> q) -> ((q -> false) -> (p -> false)) :=
    fun hhp negq => -- We are given a function hhp which takes in hp and returns hq, AND we are given that hq returns false
        fun hp => -- We want a function that takes in ¬Q (a function which takes in hq and returns false) and outputs ¬P (a function that takes in hp and returns false)
            negq (hhp hp) -- Recall negq takes in q and returns False, so our goals are accomplished
