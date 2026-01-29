variable (alpha : Type)
variable (p: alpha -> Prop)
variable (q: Prop)

-- Prove existentiation - if we have w of type alpha, and we know (p alpha) is true, then ∃ x, p x
example: (a : alpha) -> (p a) -> (Exists fun x => p x) :=
  fun w => fun hp_of_w => ⟨ w, hp_of_w ⟩

-- Use existentiation - Exists.elim (proof) (handler)
example: (∃x, p x) -> (∀z, (p z -> q)) -> q :=
  fun exist_w => -- We have w of type alpha and we know (p w) is True
      fun hp_to_q => -- We know that ∀x, (p x)→q
        Exists.elim (exist_w) (hp_to_q) -- So we get q
