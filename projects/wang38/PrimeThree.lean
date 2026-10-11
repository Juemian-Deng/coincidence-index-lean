import BalancedReflection
import SmallDimensions

/-! Complete, nonvacuous published part-(i) theorem for p=3 and all n≤8.
This finite-prime subtheorem does not stand in for the all-prime target. -/
open scoped BigOperators
namespace Wang38I
open Wang38

lemma sumI_mod_congr {p n : ℕ} (a b : IVector n)
    (h : ∀ i, a i % (p : ℤ) = b i % (p : ℤ)) :
    sumI a % (p : ℤ) = sumI b % (p : ℤ) := by
  simp only [sumI, List.sum_ofFn]
  calc
    _ = (∑ i, a i % (p : ℤ)) % (p : ℤ) := Finset.sum_int_mod _ _ _
    _ = (∑ i, b i % (p : ℤ)) % (p : ℤ) := by simp_rw [h]
    _ = _ := (Finset.sum_int_mod _ _ _).symm

lemma prime_three_dimension {n : ℕ} (v : IVector n) (hv : Admissible 3 v) :
    n % 3 = 0 := by
  have hsq : ∀ i, (v i * v i) % 3 = 1 := by
    intro i
    have h := hv.1 i
    have hm := Int.emod_nonneg (v i) (by decide : (3 : ℤ) ≠ 0)
    have hl := Int.emod_lt_of_pos (v i) (by decide : (0 : ℤ) < 3)
    have hc : v i % 3 = 1 ∨ v i % 3 = 2 := by omega
    rw [Int.mul_emod]
    rcases hc with hc | hc <;> rw [hc] <;> decide
  have he := sumI_mod_congr (p := 3) (fun i => v i * v i) (fun _ => 1)
    (fun i => by simpa using hsq i)
  have hn : (n : ℤ) % 3 = 0 := by
    rw [← hv.2.2]
    simpa [dotI, sumI, List.sum_ofFn] using he.symm
  exact_mod_cast hn

 theorem prime_three_dimension_three (v : IVector 3) (hv : Admissible 3 v) :
    ∃ Q : QMatrix 3, PublishedGeneratedPrimitive 3 v Q := by
  have hp : OddPrime 3 := ⟨by decide, by decide, (Nat.prime_def.mp (by decide : Nat.Prime 3)).2⟩
  apply uniform_residue_exists hp v (v 0) (hv.1 0)
  have hs : (v 0 + (v 1 + v 2)) % 3 = 0 := by
    simpa [sumI, List.ofFn_succ] using hv.2.1
  have h0 := hv.1 (0 : Fin 3)
  have h1 := hv.1 (1 : Fin 3)
  have h2 := hv.1 (2 : Fin 3)
  intro i
  fin_cases i <;> norm_num at * <;> omega

/-- The canonical sign representative of a nonzero residue modulo 3. -/
def ternarySign {n : ℕ} (v : IVector n) : IVector n := fun i =>
  if v i % 3 = 1 then 1 else -1

lemma ternarySign_spec {n : ℕ} (v : IVector n) (hv : FullSupport 3 v) :
    (∀ i, ternarySign v i = 1 ∨ ternarySign v i = -1) ∧
    (∀ i, ternarySign v i % 3 = v i % 3) := by
  constructor
  · intro i; dsimp [ternarySign]; split_ifs <;> simp
  · intro i
    have h := hv i
    have hm := Int.emod_nonneg (v i) (by decide : (3 : ℤ) ≠ 0)
    have hl := Int.emod_lt_of_pos (v i) (by decide : (0 : ℤ) < 3)
    dsimp [ternarySign]
    split_ifs with he <;> omega

lemma sign_norm {n : ℕ} (s : IVector n) (hs : ∀ i, s i = 1 ∨ s i = -1) :
    dotI s s = n := by
  have hsq : ∀ i, s i * s i = 1 := by
    intro i; rcases hs i with h | h <;> rw [h] <;> decide
  simp [dotI, sumI, hsq]

lemma sign_sum_bounds {n : ℕ} (s : IVector n) (hs : ∀ i, s i = 1 ∨ s i = -1) :
    -(n : ℤ) ≤ sumI s ∧ sumI s ≤ n := by
  have hlo : ∑ _i : Fin n, (-1 : ℤ) ≤ ∑ i, s i := by
    apply Finset.sum_le_sum
    intro i _; rcases hs i with h | h <;> omega
  have hhi : ∑ i, s i ≤ ∑ _i : Fin n, (1 : ℤ) := by
    apply Finset.sum_le_sum
    intro i _; rcases hs i with h | h <;> omega
  simpa [sumI, List.sum_ofFn] using And.intro hlo hhi

lemma sign_sum_max {n : ℕ} (s : IVector n) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (he : sumI s = n) : ∀ i, s i = 1 := by
  have hh : ∀ i ∈ (Finset.univ : Finset (Fin n)), s i ≤ (1 : ℤ) := by
    intro i _; rcases hs i with h | h <;> omega
  have hh' := (Finset.sum_eq_sum_iff_of_le hh).mp (by simpa [sumI, List.sum_ofFn] using he)
  exact fun i => hh' i (Finset.mem_univ i)

lemma sign_sum_min {n : ℕ} (s : IVector n) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (he : sumI s = -(n : ℤ)) : ∀ i, s i = -1 := by
  have hh : ∀ i ∈ (Finset.univ : Finset (Fin n)), (-1 : ℤ) ≤ s i := by
    intro i _; rcases hs i with h | h <;> omega
  have hh' := (Finset.sum_eq_sum_iff_of_le hh).mp (by simpa [sumI, List.sum_ofFn] using he.symm)
  exact fun i => (hh' i (Finset.mem_univ i)).symm

 theorem prime_three_dimension_six (v : IVector 6) (hv : Admissible 3 v) :
    ∃ Q : QMatrix 6, PublishedGeneratedPrimitive 3 v Q := by
  have hp : OddPrime 3 := ⟨by decide, by decide, (Nat.prime_def.mp (by decide : Nat.Prime 3)).2⟩
  let s := ternarySign v
  obtain ⟨hs, hsv⟩ := ternarySign_spec v hv.1
  change (∀ i, s i = 1 ∨ s i = -1) at hs
  change (∀ i, s i % 3 = v i % 3) at hsv
  have hnorm : dotI s s = 6 := sign_norm s hs
  have hmod : sumI s % 3 = 0 := (sumI_mod_congr (p := 3) s v hsv).trans hv.2.1
  have hpar := norm_sum_parity s
  rw [hnorm] at hpar
  have hb := sign_sum_bounds s hs
  have hcases : sumI s = -6 ∨ sumI s = 0 ∨ sumI s = 6 := by omega
  rcases hcases with hneg | hzero | hpos
  · have hall := sign_sum_min s hs hneg
    apply double_uniform_residue_exists hp v (-1) (by decide)
    intro i
    change v i % 3 = _
    rw [← hsv, hall]
    norm_num
  · exact balanced_reflection_exists hp v s hzero hnorm
      ⟨0, by change s 0 % 3 ≠ 0; rw [hsv]; exact hv.1 0⟩ hsv
  · have hall := sign_sum_max s hs hpos
    apply double_uniform_residue_exists hp v 1 (by decide)
    intro i
    change v i % 3 = _
    rw [← hsv, hall]
    norm_num

/-- Full original part-(i) statement for the prime 3, all 1≤n≤8,
and every admissible integer vector. -/
theorem published_conjecture38I_prime_three {n : ℕ} (hn : 0 < n) (hn8 : n ≤ 8)
    (v : IVector n) (hv : Admissible 3 v) :
    ∃ Q : QMatrix n, PublishedGeneratedPrimitive 3 v Q := by
  have hdim := prime_three_dimension v hv
  have hc : n = 3 ∨ n = 6 := by omega
  rcases hc with rfl | rfl
  · exact prime_three_dimension_three v hv
  · exact prime_three_dimension_six v hv

#print axioms published_conjecture38I_prime_three
end Wang38I
