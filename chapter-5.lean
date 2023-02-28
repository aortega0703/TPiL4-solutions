-- Chapter 3
variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro <;>
  . intro h
    apply And.intro h.right h.left

example : p ∨ q ↔ q ∨ p := by
  apply Iff.intro <;>
  . intro h
    cases h with
    | inl hp => apply Or.inr hp
    | inr hq => apply Or.inl hq

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  apply Iff.intro
  . intro h
    apply And.intro h.left.left (And.intro h.left.right h.right)
  . intro h
    apply And.intro (And.intro h.left h.right.left) h.right.right

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  apply Iff.intro
  . intro h
    cases h with
    | inl hl => 
      cases hl with
      | inl hll => apply Or.inl hll
      | inr hlr => apply Or.inr (Or.inl hlr)
    | inr hr => apply Or.inr (Or.inr hr)
  . intro h
    cases h with
    | inl hl => apply Or.inl (Or.inl hl)
    | inr hr =>
      cases hr with
      | inl hrl => apply Or.inl (Or.inr hrl)
      | inr hrr => apply Or.inr hrr

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro ⟨h1, h2⟩
    cases h2 with
    | inl h2l => apply Or.inl ⟨h1, h2l⟩
    | inr h2r => apply Or.inr ⟨h1, h2r⟩
  . intro h
    cases h with
    | inl hl => apply And.intro hl.left (Or.inl hl.right)
    | inr hr => apply And.intro hr.left (Or.inr hr.right)

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  . intro h
    cases h with
    | inl hl => apply And.intro (Or.inl hl) (Or.inl hl)
    | inr hr => apply And.intro (Or.inr hr.left) (Or.inr hr.right)
  . intro h
    cases h.left with
    | inl hl => apply Or.inl hl
    | inr hr =>
      cases h.right with
      | inl hl => apply Or.inl hl
      | inr hrr => apply Or.inr ⟨hr, hrr⟩

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  apply Iff.intro
  . intro h h2
    apply (h h2.left) h2.right
  . intro h hp hq
    apply h (And.intro hp hq)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  apply Iff.intro
  . intro h
    constructor
    . intro hp
      apply h (Or.inl hp)
    . intro hq
      apply h (Or.inr hq)
  . intro h h2
    apply Or.elim h2 h.left h.right

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  apply Iff.intro
  . intro h
    constructor
    intro hp
    . apply h (Or.inl hp)
    intro hq
    . apply h (Or.inr hq)
  . intro h h2
    apply h2.elim h.left h.right

example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro h h2
  cases h with
  | inl hl => apply hl h2.left
  | inr hr => apply hr h2.right
 
example : ¬(p ∧ ¬p) := by
  admit

example : p ∧ ¬q → ¬(p → q) := by
  admit

example : ¬p → (p → q) := by
  admit
  
example : (¬p ∨ q) → (p → q) := by
  admit

example : p ∨ False ↔ p := by
  admit

example : p ∧ False ↔ False := by
  admit
  
example : (p → q) → (¬q → ¬p) := by
  admit

open Classical

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  admit
  
example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  admit

example : ¬(p → q) → p ∧ ¬q := by
  admit

example : (p → q) → (¬p ∨ q) := by
  admit

example : (¬q → ¬p) → (p → q) := by
  admit

example : p ∨ ¬p := by
  admit

example : (((p → q) → p) → p) := by
  admit

example (p q r : Prop) (hp : p)
  : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  admit