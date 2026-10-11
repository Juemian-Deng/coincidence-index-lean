import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Cast.Lemmas
import Wang38Targets
import FrequencyInequality

/-!
A bridge from actual nonzero integer-vector coordinates to the proved
histogram inequality. No histogram-realizability or moment identity is assumed.
-/
open scoped BigOperators
namespace Wang38

/-- The actual number of coordinates with integer magnitude `t`. -/
def magnitudeCount {n : Nat} (u : IVector n) (t : Nat) : Nat :=
  (Finset.univ.filter fun i => (u i).natAbs = t).card

/-- A concrete bound for every coordinate's magnitude. -/
def maxMagnitude {n : Nat} (u : IVector n) : Nat :=
  Finset.univ.sup fun i => (u i).natAbs

theorem magnitude_le_max {n : Nat} (u : IVector n) (i : Fin n) :
    (u i).natAbs ≤ maxMagnitude u :=
  Finset.le_sup (f := fun i => (u i).natAbs) (Finset.mem_univ i)

theorem sumN_eq_sum_range (N : Nat) (f : Nat → Int) :
    Frequency.sumN N f = ∑ k ∈ Finset.range N, f k := by
  induction N with
  | zero => simp [Frequency.sumN]
  | succ N ih => simp [Frequency.sumN, Finset.sum_range_succ, ih]

/-- Finite counting establishes every weighted histogram moment. -/
theorem magnitude_histogram_moment {n N : Nat} (u : IVector n)
    (hu : ∀ i, u i ≠ 0) (hN : ∀ i, (u i).natAbs ≤ N) (F : Nat → Int) :
    Frequency.sumN N (fun k => (magnitudeCount u (k+1) : Int) * F (k+1)) =
      ∑ i, F (u i).natAbs := by
  have hpos : ∀ i, 0 < (u i).natAbs := by
    intro i
    exact Int.natAbs_pos.mpr (hu i)
  rw [sumN_eq_sum_range]
  calc
    _ = ∑ k ∈ Finset.range N,
        ∑ i ∈ Finset.univ.filter (fun i => (u i).natAbs = k+1), F (u i).natAbs := by
      apply Finset.sum_congr rfl
      intro k hk
      symm
      calc
        _ = ∑ _i ∈ Finset.univ.filter (fun i => (u i).natAbs = k+1), F (k+1) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [(Finset.mem_filter.mp hi).2]
        _ = _ := by simp [magnitudeCount]
    _ = ∑ k ∈ Finset.range N,
        ∑ i ∈ Finset.univ.filter (fun i => (u i).natAbs-1 = k), F (u i).natAbs := by
      apply Finset.sum_congr rfl
      intro k hk
      have he : Finset.univ.filter (fun i : Fin n => (u i).natAbs = k+1) =
          Finset.univ.filter (fun i : Fin n => (u i).natAbs-1 = k) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have := hpos i
        omega
      rw [he]
    _ = _ := by
      apply Finset.sum_fiberwise_of_maps_to
      intro i hi
      exact Finset.mem_range.mpr (by have := hpos i; have := hN i; omega)

theorem magnitude_histogram_mass {n N : Nat} (u : IVector n)
    (hu : ∀ i, u i ≠ 0) (hN : ∀ i, (u i).natAbs ≤ N) :
    Frequency.mass N (magnitudeCount u) = (n : Int) := by
  simpa [Frequency.mass] using magnitude_histogram_moment u hu hN (fun _ => 1)

theorem magnitude_histogram_squareMass {n N : Nat} (u : IVector n)
    (hu : ∀ i, u i ≠ 0) (hN : ∀ i, (u i).natAbs ≤ N) :
    Frequency.squareMass N (magnitudeCount u) = dotI u u := by
  have h := magnitude_histogram_moment u hu hN (fun t => (t : Int)*(t : Int))
  have hs : (∑ i, ((u i).natAbs : Int)*((u i).natAbs : Int)) = dotI u u := by
    simp only [dotI, sumI, List.sum_ofFn]
    apply Finset.sum_congr rfl
    intro i hi
    exact_mod_cast (Int.natAbs_mul_self (a := u i))
  simpa only [Frequency.squareMass, mul_assoc, hs] using h

/-- The histogram inequality applied to the actual coordinates of `u`. -/
theorem vector_frequency_bound {n s m : Nat} (u : IVector n)
    (hu : ∀ i, u i ≠ 0) (hs : 1 ≤ s) (hm : 0 < m)
    (hattain : magnitudeCount u s = m)
    (hmax : ∀ t, 1 ≤ t → magnitudeCount u t ≤ m) :
    (s : Int)*(n : Int) + (m : Int)*((s : Int)-1) ≤ dotI u u := by
  have hsN : s ≤ maxMagnitude u := by
    have hcard : 0 < (Finset.univ.filter fun i => (u i).natAbs = s).card := by
      change 0 < magnitudeCount u s
      rw [hattain]
      exact hm
    rcases Finset.card_pos.mp hcard with ⟨i, hi⟩
    have he := (Finset.mem_filter.mp hi).2
    rw [← he]
    exact magnitude_le_max u i
  have h := Frequency.most_frequent_magnitude (maxMagnitude u) s m
    (magnitudeCount u) hs hsN (fun t ht _ => hmax t ht) hattain
  rw [magnitude_histogram_mass u hu (magnitude_le_max u),
    magnitude_histogram_squareMass u hu (magnitude_le_max u)] at h
  exact h

/-- The desired dimension bound follows from the actual vector's norm. -/
theorem vector_frequency_dimension_bound {n s m p : Nat} (u : IVector n)
    (hu : ∀ i, u i ≠ 0) (hs : 1 ≤ s) (hm : 0 < m)
    (hattain : magnitudeCount u s = m)
    (hmax : ∀ t, 1 ≤ t → magnitudeCount u t ≤ m)
    (hnorm : dotI u u = 2*(p : Int)*(s : Int)) : n ≤ 2*p := by
  have h := vector_frequency_bound u hu hs hm hattain hmax
  have hn : 0 ≤ (m : Int)*((s : Int)-1) :=
    Int.mul_nonneg (by omega) (by omega)
  rw [hnorm] at h
  have hl : (s : Int)*(n : Int) ≤ (s : Int)*(2*(p : Int)) := by grind
  have hb := Int.le_of_mul_le_mul_left hl (by omega)
  omega

#print axioms magnitude_histogram_moment
#print axioms vector_frequency_bound
#print axioms vector_frequency_dimension_bound
end Wang38
