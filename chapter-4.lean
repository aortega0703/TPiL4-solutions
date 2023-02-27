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

example : α → ((∀ x : α, r) ↔ r) := sorry
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry
-- try it 
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := sorry
-- try it 
def even (n : Nat) : Prop := sorry

def prime (n : Nat) : Prop := sorry

def infinitely_many_primes : Prop := sorry

def Fermat_prime (n : Nat) : Prop := sorry

def infinitely_many_Fermat_primes : Prop := sorry

def goldbach_conjecture : Prop := sorry

def Goldbach's_weak_conjecture : Prop := sorry

def Fermat's_last_theorem : Prop := sorry
