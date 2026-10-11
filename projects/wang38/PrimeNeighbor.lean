import NormLift
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
An actual integral prime-neighbor in rational Euclidean space. This module
constructs a ℤ-submodule, rather than postulating a lattice with the desired
properties. `neighbor` is exactly M + ℤ(u/p) when p is nonzero.
-/
open scoped BigOperators
namespace Wang38I
open Wang38
abbrev QVector (n : ℕ) := Fin n → ℚ

def dotQ {n : ℕ} (x y : QVector n) : ℚ := ∑ i, x i * y i

def castVector {n : ℕ} (m : IVector n) : QVector n := fun i => (m i : ℚ)

lemma dotQ_comm {n : ℕ} (x y : QVector n) : dotQ x y = dotQ y x := by
  simp [dotQ, mul_comm]

lemma dotQ_add_left {n : ℕ} (x y z : QVector n) :
    dotQ (x + y) z = dotQ x z + dotQ y z := by
  simp [dotQ, add_mul, Finset.sum_add_distrib]

lemma dotQ_add_right {n : ℕ} (x y z : QVector n) :
    dotQ x (y + z) = dotQ x y + dotQ x z := by
  simp [dotQ, mul_add, Finset.sum_add_distrib]

lemma dotQ_mul_left {n : ℕ} (a : ℚ) (x y : QVector n) :
    dotQ (fun i => a * x i) y = a * dotQ x y := by
  simp [dotQ, mul_assoc, Finset.mul_sum]

lemma dotQ_mul_right {n : ℕ} (a : ℚ) (x y : QVector n) :
    dotQ x (fun i => a * y i) = a * dotQ x y := by
  rw [dotQ_comm, dotQ_mul_left, dotQ_comm]

lemma dotQ_cast {n : ℕ} (m r : IVector n) :
    dotQ (castVector m) (castVector r) = (dotI m r : ℚ) := by
  simp [dotQ, castVector, dotI, sumI, List.sum_ofFn]

/-- The neighbor, encoded by its exact integer generator representation.
The scaled equality avoids any hidden divisibility or rounding convention. -/
def neighbor (p : ℕ) {n : ℕ} (u : IVector n) : Submodule ℤ (QVector n) where
  carrier := {x | ∃ m : IVector n, ∃ k : ℤ,
    (p : ℤ) ∣ dotI m u ∧ ∀ i, (p : ℚ) * x i = p * (m i : ℚ) + k * (u i : ℚ)}
  zero_mem' := by
    refine ⟨0, 0, ?_, ?_⟩ <;> simp [dotI, sumI]
  add_mem' := by
    rintro x y ⟨m, k, hm, hx⟩ ⟨r, l, hr, hy⟩
    refine ⟨m + r, k + l, ?_, ?_⟩
    · have he : dotI (m + r) u = dotI m u + dotI r u := by
        rw [dotI_comm]
        change dotI u (fun i => m i + r i) = _
        rw [dotI_add_right, dotI_comm u m, dotI_comm u r]
      rw [he]
      exact dvd_add hm hr
    · intro i
      simp only [Pi.add_apply, Int.cast_add]
      rw [mul_add, hx, hy]
      ring
  smul_mem' := by
    rintro a x ⟨m, k, hm, hx⟩
    refine ⟨fun i => a * m i, a * k, ?_, ?_⟩
    · rw [dotI_comm, dotI_smul_right, dotI_comm]
      exact dvd_mul_of_dvd_right hm a
    · intro i
      simp only [Pi.smul_apply, zsmul_eq_mul, Int.cast_mul]
      calc
        _ = (a : ℚ) * ((p : ℚ) * x i) := by ring
        _ = _ := by rw [hx]; ring

lemma mem_neighbor_iff {p n : ℕ} {u : IVector n} {x : QVector n} :
    x ∈ neighbor p u ↔ ∃ m : IVector n, ∃ k : ℤ,
      (p : ℤ) ∣ dotI m u ∧ ∀ i, (p : ℚ) * x i = p * (m i : ℚ) + k * (u i : ℚ) := Iff.rfl

lemma base_mem_neighbor {p n : ℕ} (u m : IVector n)
    (hm : (p : ℤ) ∣ dotI m u) : castVector m ∈ neighbor p u := by
  exact ⟨m, 0, hm, by simp [castVector]⟩

lemma lift_mem_neighbor {p n : ℕ} (hp : p ≠ 0) (u : IVector n) :
    (fun i => (u i : ℚ) / p) ∈ neighbor p u := by
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  refine ⟨0, 1, by simp [dotI, sumI], ?_⟩
  intro i
  simp [mul_div_cancel₀, hpQ]

/-- Every neighbor vector has denominator dividing p and its numerator is
in the specified one-dimensional residue class. -/
theorem neighbor_numerator {p n : ℕ} {u : IVector n} {x : QVector n}
    (hx : x ∈ neighbor p u) :
    ∃ a : IVector n, (∀ i, (a i : ℚ) = (p : ℚ) * x i) ∧
      ∃ k : ℤ, ∀ i, a i % (p : ℤ) = (k * u i) % (p : ℤ) := by
  obtain ⟨m, k, hm, hx⟩ := hx
  refine ⟨fun i => (p : ℤ) * m i + k * u i, ?_, k, ?_⟩
  · intro i
    push_cast
    exact (hx i).symm
  · intro i
    simp [Int.add_emod]

/-- Integral pairings on the actual constructed submodule. -/
theorem neighbor_integral {p n : ℕ} (hp : p ≠ 0) (u : IVector n)
    (hu : (p : ℤ) * p ∣ dotI u u)
    {x y : QVector n} (hx : x ∈ neighbor p u) (hy : y ∈ neighbor p u) :
    Integral (dotQ x y) := by
  obtain ⟨m, k, ⟨r, hr⟩, hx⟩ := hx
  obtain ⟨a, l, ⟨s, hs⟩, hy⟩ := hy
  obtain ⟨t, ht⟩ := hu
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  refine ⟨dotI m a + l * r + k * s + k * l * t, ?_⟩
  have hx' : (fun i => (p : ℚ) * x i) =
      (fun i => (p : ℚ) * castVector m i) + (fun i => (k : ℚ) * castVector u i) := by
    funext i; exact hx i
  have hy' : (fun i => (p : ℚ) * y i) =
      (fun i => (p : ℚ) * castVector a i) + (fun i => (l : ℚ) * castVector u i) := by
    funext i; exact hy i
  have he : (p : ℚ) * p * dotQ x y =
      (p : ℚ) * p * ((dotI m a + l * r + k * s + k * l * t : ℤ) : ℚ) := by
    calc
      _ = dotQ (fun i => (p : ℚ) * x i) (fun i => (p : ℚ) * y i) := by
        rw [dotQ_mul_left, dotQ_mul_right]; ring
      _ = _ := by
        rw [hx', hy', dotQ_add_left, dotQ_add_right, dotQ_add_right]
        simp only [dotQ_mul_left, dotQ_mul_right, dotQ_cast]
        rw [dotI_comm u a, hr, hs, ht]
        push_cast
        ring
  exact mul_left_cancel₀ (mul_ne_zero hpQ hpQ) he

/-- The ambient norm is positive definite on this submodule. -/
theorem neighbor_positive {p n : ℕ} {u : IVector n} {x : QVector n}
    (_hx : x ∈ neighbor p u) (h : x ≠ 0) : 0 < dotQ x x := by
  have hnonneg : 0 ≤ dotQ x x := Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  have hne : dotQ x x ≠ 0 := by
    exact fun hz => h (dotProduct_self_eq_zero.mp hz)
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

#print axioms neighbor_integral
#print axioms neighbor_numerator
#print axioms neighbor_positive
end Wang38I
