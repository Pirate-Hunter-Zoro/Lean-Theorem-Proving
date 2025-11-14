-- https://lean-lang.org/theorem_proving_in_lean4/
-- ⟨ is '\langle' and ⟩ is '\rangle'

def m : Nat := 1 -- m is a natural number

variable {p : Prop} -- object of a particular type that can be reused - in this case that type is of type 'Prop' or proposition
variable {q : Prop}
-- "insignificance of the consequent"
theorem t1 : p → q → p := fun hp : p => fun hq : q => hp -- this is a "closure"
-- Given some proposition p, it is true that for any porposition p pmaps to,  - if p exists and gives you

example (hp : p) (hq : q) : p ∧ q := And.intro hp hq -- And.into is a function that just takes in the following arguments

-- Built in proof by contradiction - given p implies q, and given not q, then we can prove not p
example (hpq : p → q) (hnq : ¬q) : ¬p :=
    fun hp : p =>
    show False from hnq (hpq hp)
-- hpq is of type "p implies q", and hnq is a thing that takes in q and gives you False

variable {p q : Prop}
example : p ∧ q ↔ q ∧ p :=
    Iff.intro
        (fun h : p ∧ q ↦
            show q ∧ p from ⟨h.right, h.left⟩ )
        (fun h : q ∧ p ↦
            show p ∧ q from And.intro (And.right h) (And.left h))

example : p ∨ q ↔ q ∨ p :=
    Iff.intro
        (fun h : p∨ q ↦
            Or.elim h
                (fun h₁ : p↦ show q ∨ p from Or.inr h₁)
                (fun h₁ : q↦ show q ∨ p from Or.inl h₁))

open Classical

example : ¬p ∨ ¬q ↔ ¬(p ∧ q) :=
    Iff.intro
        (fun h : ¬p ∨ ¬q ↦
            Or.elim h
                (fun h₁ : ¬p ↦
                    show ¬(p ∧ q) from
                    fun h₂ : p ∧ q ↦
                        show False from absurd h₂.left h₁)
                (fun h₁ : ¬q ↦
                    show ¬(p ∧ q) from
                    fun h₂ : p∧ q ↦
                        show False from absurd h₂.right h₁))
        (fun h : ¬(p ∧ q) ↦
            Or.elim (em p) -- exclusive middle only allowed with Classical package
                (fun h₁ : p ↦
                    Or.elim (em q)
                        (fun h₂ : q ↦ absurd ⟨h₁,h₂⟩ h)
                        (fun h₂ : ¬q ↦ Or.inr h₂)
                        )
                (fun h₁ : ¬p ↦ Or.inl h₁)
        )

universe u

namespace Hidden

    /- w : String, |(ww)^R| = 2*|w| -/

    inductive String (σ : Type u) where
        | empty : String σ
        | char (a : σ) : String σ
        | cons (v : String σ) (a : σ) : String σ

    #eval String.cons (String.char 1) 2

    def String.length : String σ → Nat
        | empty => 0
        | char _ => 1
        | cons (v : String σ) _ => v.length + 1

    def String.reverseInto {σ} : String σ → String σ → String σ
        | empty, w => w
        | char (a : σ), w => w.cons a
        | cons (v : String σ) (a : σ), w => v.reverseInto (w.cons a)

    def String.reverse (w : String σ) : String σ :=
        w.reverseInto String.empty

    #eval (String.cons (String.char 1) 2).reverse

end Hidden
