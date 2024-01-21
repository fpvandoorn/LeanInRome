import Mathlib

open Set Function Classical

set_option autoImplicit false


/- # Exercises in the tutorial -/

/- ## Sets-/

example (α : Type) (s t w : Set α) (hst : s ⊆ t) (htw : t ⊆ w) : s ⊆ w := by
  intro x hx
  apply htw
  apply hst
  exact hx

example (α : Type) (s t : Set α) (h : s ⊆ t) : s \ t = ∅ := by
  ext x
  constructor
  · intro ⟨hxs, hxnt⟩
    -- by_contra
    exact hxnt (h hxs)
  · intro H
    contradiction

/- ## Functions-/

example (α β : Type) (S : Set α) (f g : S → β) : f = g ↔ ∀ a : α,
  -- a ∈ S → f a = g a :=
  (ha : a ∈ S) → f ⟨a, ha⟩ = g ⟨a, ha⟩ := by
  constructor
  · intro hfg a ha
    rw [hfg]
  · intro H
    funext ⟨a, ha⟩
    specialize H a ha
    exact H

example (α β : Type) (f : α → β) : Set α → Set β := by
  intro S
  use f '' S

-- END?

example (x : ℕ) : x ∈ ({1, 2, 3, 4} : Set ℕ) ∩ {1, 3} ↔ x = 1 ∨ x = 3 := by
  constructor
  · exact fun ⟨_, _⟩ => by assumption
  · rintro (h1 | h2)
    · exact ⟨Or.intro_left _ h1, Or.intro_left _ h1⟩
    · constructor
      · right; right; left; exact h2
      · right; exact h2

example : ({a | a ≤ 0} : Set ℤ) ∪ {a | a ≥ 0} = univ := by
  ext x
  constructor
  · intro
    trivial
  · intro H
    rcases x with (hpos | hneg)
    · right
      apply Int.ofNat_nonneg
    · left
      apply le_of_lt (Int.negSucc_lt_zero hneg)

/- # Sets-/


/- The following example comes from `Mathematics in Lean` -/
example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro a ⟨haPrime, haGT⟩ H
  rw [even_iff_two_dvd, Nat.dvd_prime_two_le haPrime <| le_of_eq <| refl _] at H
  exact (LE.le.gt_iff_ne (le_of_eq H)).mp haGT H.symm


/- # Functions-/
variable (α β : Type)
-- [FAE] This two are important!

example (f : α → β) : range f = f '' univ := by
  ext y
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_, hx⟩
    tauto
  · rintro ⟨x, _, hx⟩
    use x


-- Why is the following a *statement* and not merely the *definition* of being injective?
example (f : α → β) : Injective f ↔ InjOn f univ := by sorry

example (α β : Type) (f : α → β) : f '' ∅ = ∅ := by
  ext
  exact ⟨fun ⟨y, h⟩ => h.1, fun h => by trivial⟩

example (α β : Type) (f : α → β) : f '' ∅ = ∅ := by
  ext
  exact ⟨fun ⟨y, h⟩ => h.1, fun h => by trivial⟩

example (α β : Type) (f : α → β) : range f = f '' univ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, (by trivial), rfl⟩
  · rintro ⟨y, -, rfl⟩
    use y

/- The following example comes from `Mathematics in Lean` -/
example (α : Type) (s v : Set α) (f : α → α) : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  refine ⟨fun h x _ => h ?_, fun h _ ⟨_, ⟨hy, hxy⟩⟩ => ?_ ⟩
  · use x
  · rw [← hxy]
    exact h hy

def g : ℕ → ℤ := fun n =>
  if Odd n then - Int.div (n-1) 2 else Int.div n 2

theorem Odd_ge_one {n : ℕ} : Odd n → 1 ≤ n := sorry

-- example (a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ≠ 0) : a ≠ - b := by
--   apply?

example : InjOn g {n | n ≠ 0} := by
  intro n hn m hm H
  by_cases h_cases : (Even n ∧ Even m) ∨ (Odd n ∧ Odd m)
  rcases h_cases with ⟨h_n, h_m⟩ | ⟨h_n, h_m⟩
  · rwa [g, if_neg <| (Nat.even_iff_not_odd).mp h_n, g, if_neg <| (Nat.even_iff_not_odd).mp h_m,
      Int.div_left_inj, Nat.cast_inj] at H<;>
    rwa [← even_iff_two_dvd, Int.even_coe_nat]
  · rwa [g, if_pos h_n, g, if_pos h_m, neg_inj, Int.div_left_inj, sub_left_inj, Nat.cast_inj]
      at H<;>
    rw [← Int.odd_coe_nat, Int.odd_iff] at h_n h_m
    exacts [Int.ModEq.dvd (id h_n.symm), Int.ModEq.dvd (id h_m.symm)]
  · wlog h_n : Even n generalizing m n
    · have to_remove : Even m := by
        simp only [not_or, not_and_or (a := Odd n), ← Nat.even_iff_not_odd] at h_cases
        exact Or.resolve_left h_cases.2 h_n
      rw [g, if_pos <| (Nat.odd_iff_not_even).mpr h_n, g, if_neg <| (Nat.even_iff_not_odd).mp
        to_remove, ← Int.div_neg, ← Int.neg_div_neg, neg_neg, Int.div_left_inj] at H
      have := @Int.neg_ne_of_pos (n -1) m ?_ ?_
      · tauto
      · rw [sub_pos, Nat.one_lt_cast, Nat.one_lt_iff_ne_zero_and_ne_one]
        refine ⟨hn, ?_⟩
        intro hf
        rw [hf, Nat.cast_one, sub_self, neg_zero, ← Nat.cast_zero, Nat.cast_inj] at H
        exact hm H.symm
      · simpa only [Nat.cast_pos] using Nat.zero_lt_of_ne_zero hm
      · simp only [← Nat.odd_iff_not_even, ← Int.odd_coe_nat, Int.odd_iff, Int.dvd_neg] at h_n ⊢
        exact Int.ModEq.dvd (id h_n.symm)
      · rw [← Int.even_coe_nat] at to_remove
        exact Even.two_dvd to_remove
    · sorry



variable {α β : Type} [Inhabited α]
variable (f : α → β)


noncomputable
def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

-- *** Introduce `apply_fun` ***
/- The following example comes from `Mathematics in Lean` -/
example : Injective f ↔ LeftInverse (inverse f) f := by
  refine ⟨fun hf x => hf <| inverse_spec (f x) (by use x), fun hf x y H => ?_⟩
  apply_fun (inverse f) at H
  rwa [hf x, hf y] at H

/- The following example comes from `Mathematics in Lean` -/
example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  · intro H x
    exact inverse_spec (h := H x)
  · intro H x
    exact ⟨(inverse f x), H x⟩

/- The following example comes from `Mathematics in Lean` -/
theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := h₁
  have h₃ : j ∉ S := by
    rw [← h] at h₂
    contradiction
  contradiction
