import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Parity
import LeanInRome.Common

open Nat

-- Here is a first theorem
example : ∀ m n : ℕ, Even n → Even (m * n) := by
  -- Say m and n are natural numbers, and assume n is even.
  intro m n h
  -- Let k be such that n = 2*k
  obtain ⟨k, hk⟩ := h
  -- We need to prove m*n is twice a natural number. Let's show it's twice m*k.
  use m * k
  -- Substitute for n,
  rw [hk]
  -- and now it's obvious.
  ring

-- These are pieces of data.
#check 2 + 2

#eval 2 + 2

def f (x : ℕ) :=
  x + 3

#check f

-- These are propositions, of type `Prop`.
#check 2 + 2 = 4

def FermatLastTheorem :=
  ∀ x y z n : ℕ, n > 2 ∧ x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n

#check FermatLastTheorem

-- These are proofs of propositions.
theorem easy : 2 + 2 = 4 :=
  rfl

#check easy

theorem hard : FermatLastTheorem :=
  sorry

#check hard

-- Here are some proofs.
example : ∀ m n : ℕ, Even n → Even (m * n) := fun m n ⟨k, (hk : n = k + k)⟩ ↦
  have hmn : m * n = m * k + m * k := by rw [hk, mul_add]
  show ∃ l, m * n = l + l from ⟨_, hmn⟩

example : ∀ m n : ℕ, Even n → Even (m * n) :=
fun m n ⟨k, hk⟩ ↦ ⟨m * k, by rw [hk, mul_add]⟩

example : ∀ m n : ℕ, Even n → Even (m * n) := by
  rintro m n ⟨k, hk⟩; use m * k; rw [hk]; ring

example : ∀ m n : ℕ, Even n → Even (m * n) := by
  intros; simp [*, parity_simps]

example : ∀ (n : ℕ), ∃ p, p.Prime ∧ p > n := by
  intro n
  let p := (n! + 1).minFac
  have hp : p.Prime := by
    apply minFac_prime
    intro h1
    simp at h1
    exact factorial_ne_zero _ h1
  use p
  constructor
  · exact hp
  · by_contra hle
    have hdvd : p ∣ n! := by
      apply (Prime.dvd_factorial hp).2
      exact not_lt.1 hle
    have hdvd' : p ∣ n! + 1 := by
      exact minFac_dvd (n ! + 1)
    have hdvdone : p ∣ 1 := by
      exact (Nat.dvd_add_right hdvd).mp hdvd'
    have hnotdvdone : ¬ p ∣ 1 := by
      exact (Nat.Prime.not_dvd_one hp)
    contradiction
