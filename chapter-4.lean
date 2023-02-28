variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  ⟨
    λ h : ∀ x, p x ∧ q x =>
      ⟨ λ x : α => (h x).left,
        λ x : α => (h x).right ⟩,
    λ h : (∀ x, p x) ∧ (∀ x, q x) =>
      λ x : α =>
        ⟨ h.left x , h.right x⟩
  ⟩

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun h1 : (∀ x, p x → q x) =>
    fun h2 : (∀ x, p x) =>
      fun x : α => (h1 x) (h2 x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun h : (∀ x, p x) ∨ (∀ x, q x) =>
    fun x : α =>
      h.elim
        (fun hl : (∀ x, p x) =>
          Or.inl (hl x))
        (fun hr : (∀ x, q x) =>
          Or.inr (hr x))

variable (r : Prop)

open Classical

example : α → ((∀ _ : α, r) ↔ r) :=
  fun a : α =>
    ⟨
      fun x : (∀ _ : α, r) => x a,
      fun y : r =>
        fun _ : α => y
    ⟩

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  ⟨
    fun h : (∀ x, p x ∨ r) =>
      show (∀ x, p x) ∨ r from
      Or.elim (em r)
        (fun hr : r => Or.inr hr)
        (fun hnr : ¬r =>
          Or.inl fun ha : α =>
            Or.elim (h ha)
              (fun hpx : (p ha) => hpx)
              (fun hr : r => absurd hr hnr)),
    fun h : (∀ x, p x) ∨ r =>
      show (∀ x, p x ∨ r) from
      fun a : α =>
        Or.elim h
          (fun hl : (∀ x, p x) => Or.inl (hl a))
          (fun hr : r => Or.inr hr)
  ⟩

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  ⟨
    λ h : (∀ x, r → p x) =>
      show (r → ∀ x, p x) from
      λ hr : r =>
        λ ha : α =>
          h ha hr,
    λ h : r → ∀ x, p x =>
      show (∀ x, r → p x) from
      λ ha : α =>
        λ hr : r =>
          h hr ha
  ⟩

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  have h2 : shaves barber barber ↔ ¬ shaves barber barber := h barber
  Or.elim (em (shaves barber barber))
    (fun h3 : shaves barber barber =>
      (h2.mp h3) h3)
    (fun h3 : ¬(shaves barber barber) =>
      h3 (h2.mpr h3))

def divides (n m : Nat) : Prop :=
  ∃ (k : Nat), k * n = m

def even (n : Nat) : Prop :=
  divides 2 n

def prime (n : Nat) : Prop :=
  ∀ (k : Nat), k != n ∧ k != n → ¬(divides k n)

def infinitely_many_primes : Prop :=
  ∀ (n : Nat), ∃ (k : Nat), k > n ∧ prime k

def Fermat_prime (n : Nat) : Prop :=
  prime n ∧ ∃ (k : Nat), (2^k + 1= n)

def infinitely_many_Fermat_primes : Prop :=
  ∀ (n : Nat), ∃ (k : Nat), k > n ∧ Fermat_prime k

def goldbach_conjecture : Prop :=
  ∀ (n : Nat), n > 2 ∧ even n → ∃ (p q : Nat), prime p ∧ prime q ∧ p + q = n

def Goldbach's_weak_conjecture : Prop :=
  ∀ (n : Nat), n > 2 ∧ even n →
    ∃ (p q r : Nat), prime p ∧ prime q ∧ prime r ∧
      p + q + r = n

def Fermat's_last_theorem : Prop :=
  ∀ (n : Nat), n > 2 →
    ¬∃ (a b c : Nat), a^n + b^n = c^n

example : (∃ _ : α, r) → r :=
  fun h : (∃ _ : α, r) =>
    h.elim (fun _: α => fun hw: r => hw)

example (a : α) : r → (∃ _ : α, r) :=
  fun h: r =>
      Exists.intro a h

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
    (fun h: (∃ x, p x ∧ r) =>
      h.elim (fun w : α => fun hw : p w ∧ r =>
        ⟨Exists.intro w (hw).left, (hw).right⟩))
    (fun ⟨⟨w, hw⟩, hr⟩ =>
      ⟨w, hw, hr⟩)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (fun h : (∃ x, p x ∨ q x) =>
      match h with
      | ⟨w, hw⟩ => Or.elim hw
        (fun hpw : p w => Or.inl ⟨w, hpw⟩)
        (fun hqw : q w => Or.inr ⟨w, hqw⟩))
    (fun h : (∃ x, p x) ∨ (∃ x, q x) =>
      Or.elim h
        (fun h1 : (∃ x, p x) =>
          let ⟨w, h1w⟩ := h1
          ⟨w, Or.inl h1w⟩)
        (fun h1 : (∃ x, q x) =>
          let ⟨w, h1w⟩ := h1
          ⟨w, Or.inr h1w⟩))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
    (fun h: (∀ x, p x) =>
      fun h2: (∃ x, ¬ p x) =>
        let ⟨w, wh2⟩ := h2
        wh2 (h w))
    (fun h: ¬(∃ x, ¬ p x) =>
      fun z: α =>
        Or.elim (em (p z))
          (fun hpz: p z => hpz)
          (fun hnpz: ¬(p z) => absurd ⟨z, hnpz⟩ h))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
    (fun h: (∃ x, p x) =>
      let ⟨w, wh⟩ := h
      fun h2: (∀ x, ¬ p x) =>
        (h2 w) wh)
    (fun h: ¬(∀ x, ¬ p x) =>
      byContradiction
        fun h2 : ¬(∃ x, p x) =>
          h fun x : α =>
            fun hx : p x =>
              h2 ⟨x, hx⟩)

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
    (fun h: (¬ ∃ x, p x) =>
      fun x : α =>
        fun hx : p x =>
          h ⟨x, hx⟩ )
    (fun h: (∀ x, ¬ p x) =>
      fun h2: (∃ x, p x) =>
        let ⟨w, hw⟩ := h2
        (h w) hw)

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro
    (fun h: (¬ ∀ x, p x) =>
      byContradiction
        fun h2 : ¬(∃ x, ¬ p x) =>
          h fun x : α =>
            Or.elim (em (p x))
              (fun hpx : p x => hpx)
              (fun hnpx : ¬(p x) => absurd ⟨x, hnpx⟩ h2 ))
    (fun h: (∃ x, ¬ p x) =>
      fun h2: (∀ x, p x) =>
        let ⟨w, hw⟩ := h
        hw (h2 w) )

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
    (fun h : (∀ x, p x → r) =>
      fun h2 : (∃ x, p x) =>
        let ⟨w, hw⟩ := h2
        (h w) hw)
    (fun h : (∃ x, p x) → r =>
      fun w : α =>
        fun hw : p w =>
          h ⟨w, hw⟩ )

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (fun ⟨b, (hb : p b → r)⟩ =>
     fun h2 : ∀ x, p x =>
     show r from hb (h2 b))
    (fun h1 : (∀ x, p x) → r =>
     show ∃ x, p x → r from
       byCases
         (fun hap : ∀ x, p x => ⟨a, λ _ => h1 hap⟩)
         (fun hnap : ¬ ∀ x, p x =>
          byContradiction
            (fun hnex : ¬ ∃ x, p x → r =>
              have hap : ∀ x, p x :=
                fun x =>
                byContradiction
                  (fun hnp : ¬ p x =>
                    have hex : ∃ x, p x → r := ⟨x, (fun hp => absurd hp hnp)⟩
                    show False from hnex hex)
              show False from hnap hap)))

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro
    (fun h : (∃ x, r → p x) =>
      fun hr : r =>
        let ⟨w, hw⟩ := h
        ⟨w, hw hr⟩ )
    (fun h : (r → ∃ x, p x) =>
      byCases
        (fun hr : r =>
          let ⟨w, hw⟩ := h hr
          ⟨w, λ _ => hw⟩  )
        (fun hnr : ¬r =>
          ⟨a, fun hr : r =>
            absurd hr hnr⟩ ))
