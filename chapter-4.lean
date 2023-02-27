-- try it 
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
-- try it 
variable (α : Type) (p q : α → Prop)
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
-- try it 
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

open Classical

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  have h2 : shaves barber barber ↔ ¬ shaves barber barber := h barber
  Or.elim (em (shaves barber barber))
    (fun h3 : shaves barber barber =>
      (h2.mp h3) h3)
    (fun h3 : ¬(shaves barber barber) =>
      h3 (h2.mpr h3))

-- try it 
def even (n : Nat) : Prop := sorry

def prime (n : Nat) : Prop := sorry

def infinitely_many_primes : Prop := sorry

def Fermat_prime (n : Nat) : Prop := sorry

def infinitely_many_Fermat_primes : Prop := sorry

def goldbach_conjecture : Prop := sorry

def Goldbach's_weak_conjecture : Prop := sorry

def Fermat's_last_theorem : Prop := sorry
