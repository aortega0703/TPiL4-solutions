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
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  ⟨ λ pqr : p ∧ (q ∨ r) =>
    pqr.2.elim
      (λ y : q =>
        Or.inl ⟨pqr.1, y⟩ )
      (λ y : r =>
        Or.inr ⟨pqr.1, y⟩ )
  , λ pqpr : (p ∧ q) ∨ (p ∧ r) =>
    pqpr.elim
      (λ pq : p ∧ q =>
        ⟨pq.1, Or.inl pq.2⟩)
      (λ pr : p ∧ r =>
        ⟨pr.1, Or.inr pr.2⟩)⟩
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  ⟨ λ pqr : p ∨ (q ∧ r) =>
    pqr.elim
      (λ x : p =>
        ⟨Or.inl x, Or.inl x⟩)
      (λ qr : q ∧ r =>
        ⟨Or.inr qr.1, Or.inr qr.2⟩),
    λ pqpr : (p ∨ q) ∧ (p ∨ r) =>
      pqpr.1.elim
        (λ x : p => Or.inl x)
        (λ x : q =>
          pqpr.2.elim
            (λ y : p => Or.inl y)
            (λ y : r => Or.inr ⟨x, y⟩)) ⟩

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (λ hpqr : p → q → r =>
        λ hpq : p ∧ q =>
          hpqr hpq.1 hpq.2)
    (λ hpqr : (p ∧ q) → r =>
        λ hp : p =>
          λ hq : q =>
            hpqr ⟨hp, hq⟩)
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  ⟨ λ h : (p ∨ q) → r =>
    ⟨ λ hp : p =>
      h (Or.inl hp)
    , λ hq : q =>
      h (Or.inr hq) ⟩
  , λ h : (p → r) ∧ (q → r) =>
    λ hpq : p ∨ q =>
      hpq.elim h.left h.right⟩
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  ⟨
    λ h : ¬(p ∨ q) =>
      ⟨ λ hp : p => h (Or.inl hp)
      , λ hq : q => h (Or.inr hq)⟩,
    λ h : ¬p ∧ ¬q =>
      λ hpq : p ∨ q =>
        hpq.elim h.left h.right
  ⟩
example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  λ h : ¬p ∨ ¬q =>
    λ hpq : p ∧ q =>
      h.elim
        (λ hnp : ¬p => hnp hpq.left)
        (λ hnq : ¬q => hnq hpq.right)
example : ¬(p ∧ ¬p) :=
  λ h : p ∧ ¬p => h.right h.left
example : p ∧ ¬q → ¬(p → q) :=
  λ h : p ∧ ¬q =>
    λ npq : p → q =>
      h.right (npq h.left)
example : ¬p → (p → q) :=
  λ hnp : ¬p =>
    λ hp : p =>
      absurd hp hnp
example : (¬p ∨ q) → (p → q) :=
  λ h : ¬p ∨ q =>
    λ hp : p =>
      h.elim
        (λ hnp : ¬p => absurd hp hnp)
        (λ hq : q => hq)
example : p ∨ False ↔ p :=
  ⟨
    λ h : p ∨ False =>
      h.elim
        (λ hp : p => hp)
        (λ hFalse : False => False.elim hFalse),
    λ h : p =>
      Or.inl h
  ⟩
example : p ∧ False ↔ False :=
  ⟨
    λ h : p ∧ False => h.right,
    λ h : False => ⟨False.elim h, h⟩
  ⟩
example : (p → q) → (¬q → ¬p) :=
  λ h : p → q =>
    λ hnq : ¬q =>
      λ hp : p =>
        hnq (h hp)

open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  λ h : p → q ∨ r =>
    (em p).elim
      (λ hp : p =>
        (h hp).elim
          (λ hq : q => Or.inl (λ _ : p => hq))
          (λ hr : r => Or.inr (λ _ : p => hr)))
      (λ hnp : ¬p =>
        Or.inl (λ hp : p => absurd hp hnp))
example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  λ h : ¬(p ∧ q) =>
    Or.elim (em p)
      (λ hp : p =>
        Or.elim (em q)
          (λ hq : q => absurd ⟨hp, hq⟩ h )
          (λ hnq : ¬q => Or.inr hnq))
      (λ hnp : ¬p => Or.inl hnp)
example : ¬(p → q) → p ∧ ¬q :=
  λ h : ¬(p → q) =>
    Or.elim (em q)
      (λ hq : q =>
        absurd (λ _ : p => hq) h)
      (λ hnq : ¬q =>
        Or.elim (em p)
          (λ hp : p => ⟨ hp, hnq ⟩)
          (λ hnp : ¬p =>
            absurd (λ hp : p => absurd hp hnp) h))
example : (p → q) → (¬p ∨ q) :=
  λ h : p → q =>
    Or.elim (em p)
      (λ hp : p => Or.inr (h hp))
      (λ hnp : ¬p => Or.inl hnp)
example : (¬q → ¬p) → (p → q) :=
  λ h : ¬q → ¬p =>
    Or.elim (em p)
      (λ hp : p =>
        Or.elim (em q)
          (λ hq : q =>
            λ _ : p => hq)
          (λ hnq : ¬q => absurd hp (h hnq)))
      (λ hnp : ¬p =>
        λ hp : p => absurd hp hnp)
example : p ∨ ¬p :=
  em p
example : (((p → q) → p) → p) :=
  λ h : (p → q) → p =>
    Or.elim (em p)
      (λ hp : p => hp)
      (λ hnp : ¬p =>
        h (λ hp : p => absurd hp hnp))