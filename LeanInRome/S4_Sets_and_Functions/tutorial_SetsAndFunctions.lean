import Mathlib

open Set Function Classical

set_option autoImplicit false

/- # Sets-/

example (α : Type) (s t w : Set α) (hst : s ⊆ t) (htw : t ⊆ w) : s ⊆ w := by sorry

-- una intersezione

example (α : Type) (s t : Set α) (h : s ⊆ t) : s \ t = ∅ := by sorry



/- # Functions-/

example (α β : Type) (S : Set α) (f g : S → β) : f = g ↔ ∀ a : α,
  a ∈ S → f a = g a := by sorry

example (α β : Type) (f : α → β) : Set α → Set β := by sorry
