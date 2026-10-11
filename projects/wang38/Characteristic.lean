import PrimeNeighbor
import Mathlib.Algebra.Ring.Int.Parity

/-! The all-ones characteristic vector of the constructed odd-prime neighbor. -/
open scoped BigOperators
namespace Wang38I
open Wang38

def ones (n : ℕ) : QVector n := fun _ => 1

lemma ones_mem_neighbor {p n : ℕ} (u : IVector n)
    (hu : sumI u % (p : ℤ) = 0) : ones n ∈ neighbor p u := by
  apply base_mem_neighbor u (fun _ => 1)
  simpa [dotI] using Int.dvd_of_emod_eq_zero hu

lemma numerator_norm {p n : ℕ} {x : QVector n} {a : IVector n}
    (ha : ∀ i, (a i : ℚ) = (p : ℚ) * x i) :
    (p : ℚ) * p * dotQ x x = (dotI a a : ℚ) := by
  have he : castVector a = fun i => (p : ℚ) * x i := funext ha
  rw [← dotQ_cast, he, dotQ_mul_left, dotQ_mul_right]
  ring

lemma numerator_sum {p n : ℕ} {x : QVector n} {a : IVector n}
    (ha : ∀ i, (a i : ℚ) = (p : ℚ) * x i) :
    (p : ℚ) * dotQ (ones n) x = (sumI a : ℚ) := by
  simp only [dotQ, ones, one_mul, sumI, List.sum_ofFn, Int.cast_sum]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => (ha i).symm

lemma norm_sum_parity {n : ℕ} (a : IVector n) :
    2 ∣ dotI a a - sumI a := by
  simp only [dotI, sumI, List.sum_ofFn, ← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro i _
  simpa [mul_sub] using (Int.even_mul_pred_self (a i)).two_dvd

/-- Exact characteristic-vector identity, proved from the source congruence
and oddness of p. No classification theorem is involved. -/
theorem ones_characteristic {p n : ℕ} (hp : OddPrime p) (u : IVector n)
    (hunorm : (p : ℤ) * p ∣ dotI u u)
    (husum : sumI u % (p : ℤ) = 0)
    {x : QVector n} (hx : x ∈ neighbor p u) :
    ∃ z : ℤ, dotQ x x - dotQ (ones n) x = (2 * z : ℤ) := by
  have hp0 : p ≠ 0 := by have := hp.1; omega
  obtain ⟨q, hq⟩ := neighbor_integral hp0 u hunorm hx hx
  obtain ⟨c, hc⟩ := neighbor_integral hp0 u hunorm (ones_mem_neighbor u husum) hx
  obtain ⟨a, ha, _⟩ := neighbor_numerator hx
  have hn : (p : ℤ) * p * q = dotI a a := by
    have hh := numerator_norm ha
    rw [hq] at hh
    exact_mod_cast hh
  have hs : (p : ℤ) * c = sumI a := by
    have hh := numerator_sum ha
    rw [hc] at hh
    exact_mod_cast hh
  have hpodd : (p : ℤ) % 2 = 1 := by exact_mod_cast hp.2.1
  have he : (p : ℤ) * p * (q - c) = dotI a a - (p : ℤ) * sumI a := by
    rw [← hn, ← hs]
    ring
  have hpn : 2 ∣ ((p : ℤ) - 1) := by omega
  have hd : 2 ∣ dotI a a - (p : ℤ) * sumI a := by
    have h1 := norm_sum_parity a
    have h2 := dvd_mul_of_dvd_left hpn (sumI a)
    convert dvd_sub h1 h2 using 1; ring
  have hz : (q - c) % 2 = 0 := by
    have hh := Int.emod_eq_zero_of_dvd hd
    rw [← he] at hh
    simpa [Int.mul_emod, hpodd] using hh
  obtain ⟨z, hz⟩ := Int.dvd_of_emod_eq_zero hz
  refine ⟨z, ?_⟩
  rw [hq, hc]
  exact_mod_cast hz

/-- Oddness is witnessed by p times a standard coordinate vector. -/
theorem neighbor_is_odd {p n : ℕ} (hp : OddPrime p) (hn : 0 < n)
    (u : IVector n) :
    ∃ x : QVector n, x ∈ neighbor p u ∧
      ∃ z : ℤ, dotQ x x = (z : ℚ) ∧ z % 2 = 1 := by
  classical
  let j : Fin n := ⟨0, hn⟩
  let m : IVector n := fun i => if i = j then (p : ℤ) else 0
  refine ⟨castVector m, base_mem_neighbor u m ?_, (p : ℤ) * p, ?_, ?_⟩
  · rw [dotI_comm]
    dsimp [m]
    rw [dotI_single]
    exact dvd_mul_left _ _
  · rw [dotQ_cast]
    congr 1
    simp [dotI, sumI, List.sum_ofFn, m]
  · have hpodd : (p : ℤ) % 2 = 1 := by exact_mod_cast hp.2.1
    rw [Int.mul_emod, hpodd]
    decide

#print axioms ones_characteristic
#print axioms neighbor_is_odd
end Wang38I
