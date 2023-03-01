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
  intro h
  apply h.right h.left

example : p ∧ ¬q → ¬(p → q) := by
  intro h1 h2
  apply h1.right (h2 h1.left)

example : ¬p → (p → q) := by
  intro h1 h2
  apply absurd h2 h1

example : (¬p ∨ q) → (p → q) := by
  intro h1 h2
  cases h1 with
  | inl hl => apply absurd h2 hl
  | inr hr => apply hr

example : p ∨ False ↔ p := by
  apply Iff.intro
  . intro h
    cases h with
    | inl hl => apply hl
    | inr hr => apply False.elim hr
  . intro h
    apply Or.inl h

example : p ∧ False ↔ False := by
  apply Iff.intro
  . intro h
    apply h.right
  . intro h
    apply False.elim h

example : (p → q) → (¬q → ¬p) := by
  intro h1 h2 h3
  apply h2 (h1 h3)

open Classical

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro h
  cases (em p) with
  | inl hp =>
    apply (h hp).elim
    . intro hq
      apply Or.inl (λ _ : p => hq)
    . intro hr
      apply Or.inr (λ _ : p => hr)
  | inr hnp =>
    apply Or.inl (λ hp : p => absurd hp hnp)

example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro h
  cases (em p) with
  | inl hp =>
    cases (em q) with
    | inl hq =>
      apply absurd (And.intro hp hq) h
    | inr hnq =>
      apply Or.inr
      assumption
  | inr hnp =>
    apply Or.inl
    assumption

example : ¬(p → q) → p ∧ ¬q := by
  intro h
  cases (em q) with
  | inl hq =>
    apply absurd (λ _ : p => hq) h
  | inr hnq =>
    cases (em p) with
    | inl hp =>
      apply And.intro
      repeat assumption
    | inr hnp =>
      exact False.elim (h (λ hp : p => absurd hp hnp))

example : (p → q) → (¬p ∨ q) := by
  intro h
  cases (em p) with
  | inl hp =>
    apply Or.inr
    exact h hp
  | inr hnp =>
    apply Or.inl
    assumption

example : (¬q → ¬p) → (p → q) := by
  intro h hp
  cases (em q) with
  | inl hq => assumption
  | inr hnq => apply absurd hp (h hnq)

example : p ∨ ¬p := by
  apply (em p)

example : (((p → q) → p) → p) := by
  intro h
  cases (em p) with
  | inl hp => assumption
  | inr hnp => apply h (λ hp : p => absurd hp hnp)

-- Chapter 4
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  apply Iff.intro
  . intro h
    constructor
    . apply (λ ha : α => (h ha).left)
    . apply (λ ha : α => (h ha).right)
  . intro h
    apply (λ ha : α => And.intro (h.left ha) (h.right ha))

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intro h1 h2
  apply (λ ha : α => (h1 ha) (h2 ha))

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro h
  cases h with
  | inl hl =>
    apply (λ ha : α => Or.inl (hl ha))
  | inr hr =>
    apply (λ ha : α => Or.inr (hr ha))

variable (r : Prop)

open Classical

example : α → ((∀ _ : α, r) ↔ r) := by
  intro h
  apply Iff.intro
  . intro hr
    apply hr h
  . intro hr _
    exact hr

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  apply Iff.intro
  . intro h
    cases (em r) with
    | inl hr => exact Or.inr hr
    | inr hnr =>
      apply Or.inl
        (λ ha : α => Or.elim (h ha)
          (λ hpa : p ha => hpa)
          (λ hr : r => absurd hr hnr))
  . intro h
    apply (λ ha : α =>
      Or.elim h
        (λ hpa : (∀ (x : α), p x) => Or.inl (hpa ha))
        (λ hr : r => Or.inr hr))

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  apply Iff.intro
  . intro h hr
    apply (λ ha : α => (h ha) hr )
  . intro h
    apply (λ ha : α =>
      λ hr : r => (h hr) ha )

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
  have hb := h barber
  cases (em (shaves barber barber)) with
  | inl hsbb => apply (hb.mp hsbb) hsbb
  | inr hnsbb => apply hnsbb (hb.mpr hnsbb)

example : (∃ _ : α, r) → r := by
  intro h
  cases h with
  | intro hx hf => apply hf

example (a : α) : r → (∃ _ : α, r) := by
  intro h
  constructor
  assumption
  assumption

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  apply Iff.intro
  . intro h
    cases h with
    | intro hx hf =>
      have hl := Exists.intro hx hf.left
      exact And.intro hl hf.right
  . intro h
    cases h.left with
    | intro hx hf => apply Exists.intro hx ⟨hf, h.right⟩

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  apply Iff.intro
  . intro h
    cases h with
    | intro hx hf =>
      cases hf with
      | inl hfl => exact Or.inl (Exists.intro hx hfl)
      | inr hfr => exact Or.inr (Exists.intro hx hfr)
  . intro h
    cases h with
    | inl hl =>
      cases hl with
      | intro hx hf => apply Exists.intro hx (Or.inl hf)
    | inr hr =>
      cases hr with
      | intro hx hf => apply Exists.intro hx (Or.inr hf)

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  apply Iff.intro
  . intro h1 h2
    cases h2 with
    | intro hx hf => exact hf (h1 hx)
  . intro h
    apply (λ ha : α =>
      Or.elim (em (p ha))
      (λ hpa : p ha => hpa)
      (λ hnpa : ¬(p ha) => absurd (Exists.intro ha hnpa) h))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
  apply Iff.intro
  . intro h1 h2
    cases h1 with
    | intro hx hf => apply (h2 hx) hf
  . intro h1
    apply (byContradiction fun h2 : ¬(∃ x, p x) =>
          h1 fun x : α =>
            fun hx : p x =>
              h2 ⟨x, hx⟩)

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  apply Iff.intro
  . intro h
    apply (λ ha : α =>
      λ hpx : p ha => h (Exists.intro ha hpx))
  . intro h1 h2
    cases h2 with
    | intro hx hf => apply (h1 hx) hf

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
  apply Iff.intro
  . intro h
    apply byContradiction
        fun h2 : ¬(∃ x, ¬ p x) =>
          h fun x : α =>
            Or.elim (em (p x))
              (fun hpx : p x => hpx)
              (fun hnpx : ¬(p x) => absurd ⟨x, hnpx⟩ h2 )
  . intro h1 h2
    cases h1 with
    | intro hx hf => apply hf (h2 hx)

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
  apply Iff.intro
  . intro h1 h2
    cases h2 with
    | intro hx hf => apply (h1 hx) hf
  . intro h
    apply (λ ha : α =>
      λ hpa : p ha => h (Exists.intro ha hpa))

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
  apply Iff.intro
  . intro h1 h2
    cases h1 with
    | intro hx hf => apply hf (h2 hx)
  . intro h
    cases em (∀ (x : α), p x) with
    | inl hem => apply Exists.intro a (λ _ : p a => h hem )
    | inr hnem =>
      apply (fun hnap : ¬ ∀ x, p x =>
        byContradiction
          (fun hnex : ¬ ∃ x, p x → r =>
            have hap : ∀ x, p x :=
              fun x =>
              byContradiction
                (fun hnp : ¬ p x =>
                  have hex : ∃ x, p x → r := ⟨x, (fun hp => absurd hp hnp)⟩
                  show False from hnex hex)
            show False from hnap hap))
      assumption

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
  apply Iff.intro
  . intro h1 h2
    cases h1 with
    | intro hx hf =>
      apply Exists.intro hx (hf h2)
  . intro h
    cases (em r) with
    | inl hl =>
      cases h hl with
      | intro hx hf =>
        apply Exists.intro hx (λ _ : r => hf)
    | inr h2 =>
      apply Exists.intro a (fun hr : r =>
            absurd hr h2)

-- Chapter 5
example (p q r : Prop) (hp : p)
  : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  repeat (first | exact Or.inl hp | exact Or.inr (Or.inl hp) | exact Or.inr (Or.inr hp) | constructor)