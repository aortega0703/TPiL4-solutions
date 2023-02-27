-- try it 
variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  ⟨ λ pq : p ∧ q => ⟨pq.2 , pq.1⟩
  , λ qp : q ∧ p => ⟨qp.2 , qp.1⟩ ⟩
example : p ∨ q ↔ q ∨ p :=
  ⟨ λ pq : p ∨ q =>
    pq.elim
      (λ x : p => Or.inr x)
      (λ x : q => Or.inl x)
  , λ qp : q ∨ p =>
    qp.elim
      (λ x : q => Or.inr x)
      (λ x : p => Or.inl x) ⟩

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  ⟨ λ x : (p ∧ q) ∧ r =>
    ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  , λ x : p ∧ (q ∧ r) =>
    ⟨⟨x.1, x.2.1⟩, x.2.2⟩ ⟩ 
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := 
  ⟨ λ pqr : (p ∨ q) ∨ r =>
    pqr.elim
      (λ pq : p ∨ q =>
        pq.elim 
          (λ x : p => Or.inl x)
          (λ x : q => Or.inr (Or.inl x)))
      (λ x : r => Or.inr (Or.inr x))
  , λ pqr : p ∨ (q ∨ r) =>
    pqr.elim
      (λ x : p => Or.inl (Or.inl x))
      (λ qr : q ∨ r =>
        qr.elim
          (λ x : q => Or.inl (Or.inr x))
          (λ x : r => Or.inr x)) ⟩

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
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry
