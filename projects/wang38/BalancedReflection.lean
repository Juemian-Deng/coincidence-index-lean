import UniformConstruction

/-! An explicit constructive family requiring a zero-sum norm-2p lift.
The lift is constructed below for the complete p=3 low-dimensional case. -/
open scoped BigOperators
namespace Wang38I
open Wang38

def reflectionMatrix (p : ℕ) {n : ℕ} (s : IVector n) : QMatrix n := fun i j =>
  (if i = j then 1 else 0) - (s i : ℚ) * (s j : ℚ) / p

def reflectionNumerator (p : ℕ) {n : ℕ} (s : IVector n) : IMatrix n := fun i j =>
  (p : ℤ) * (if i = j then 1 else 0) - s i * s j

lemma reflection_orthogonal {p n : ℕ} (hp : p ≠ 0) (s : IVector n)
    (hs : dotI s s = 2 * (p : ℤ)) : Orthogonal (reflectionMatrix p s) := by
  classical
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  let P : Matrix (Fin n) (Fin n) ℚ := Matrix.vecMulVec (castVector s) (castVector s)
  have hP : P * P = (2 * (p : ℚ)) • P := by
    dsimp [P]
    rw [Matrix.vecMulVec_mul_vecMulVec]
    have hn : dotProduct (castVector s) (castVector s) = 2 * (p : ℚ) := by
      change dotQ _ _ = _
      rw [dotQ_cast, hs]
      push_cast
      rfl
    rw [hn]
    ext i j
    simp only [Matrix.vecMulVec, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hQ : Matrix.of (reflectionMatrix p s) = 1 - (p : ℚ)⁻¹ • P := by
    ext i j
    simp [reflectionMatrix, Matrix.one_apply, P, Matrix.vecMulVec, castVector, div_eq_mul_inv]
    ring
  have hgram : (Matrix.of (reflectionMatrix p s)).transpose * Matrix.of (reflectionMatrix p s) = 1 := by
    rw [hQ]
    have hPt : P.transpose = P := Matrix.transpose_vecMulVec _ _
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, hPt]
    simp only [mul_sub, sub_mul, one_mul, mul_one,
      Matrix.smul_mul, Matrix.mul_smul, hP]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    field_simp
    ring
  intro i j
  have h := congrFun (congrFun hgram i) j
  simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, sumQ, List.sum_ofFn] using h

lemma reflection_regular {p n : ℕ} (s : IVector n) (hs : sumI s = 0) :
    Regular (reflectionMatrix p s) := by
  classical
  intro i
  simp only [sumQ, List.sum_ofFn, reflectionMatrix, Finset.sum_sub_distrib]
  have hz : ∑ j : Fin n, (s j : ℚ) = 0 := by
    exact_mod_cast (show ∑ j : Fin n, s j = 0 by simpa [sumI, List.sum_ofFn] using hs)
  simp [div_eq_mul_inv, ← Finset.sum_mul, ← Finset.mul_sum, hz]

lemma reflection_numerator {p n : ℕ} (hp : p ≠ 0) (s : IVector n) :
    Numerator p (reflectionMatrix p s) (reflectionNumerator p s) := by
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  intro i j
  simp only [reflectionMatrix, reflectionNumerator]
  split_ifs <;> push_cast <;> field_simp

/-- The explicit reflection supplies the exact published matrix whenever a
zero-sum norm-2p integral representative is present. -/
theorem balanced_reflection_exists {p n : ℕ} (hp : OddPrime p)
    (v s : IVector n) (hsum : sumI s = 0) (hnorm : dotI s s = 2 * (p : ℤ))
    (hsnz : ∃ i, s i % (p : ℤ) ≠ 0)
    (hsv : ∀ i, s i % (p : ℤ) = v i % (p : ℤ)) :
    ∃ Q : QMatrix n, PublishedGeneratedPrimitive p v Q := by
  classical
  let : Fact (Nat.Prime p) := ⟨oddPrime_isPrime hp⟩
  have hp0 : p ≠ 0 := by have := hp.1; omega
  have hline : ColumnsInLine p v (reflectionNumerator p s) := by
    intro j
    refine ⟨-s j, ?_⟩
    intro i
    apply (ZMod.intCast_eq_intCast_iff' _ _ p).mp
    have hsi : (s i : ZMod p) = (v i : ZMod p) :=
      (ZMod.intCast_eq_intCast_iff' _ _ p).mpr (hsv i)
    simp only [reflectionNumerator]
    push_cast
    simp only [ZMod.natCast_self, zero_mul, zero_sub, hsi]
    ring
  have hnz : ∃ i j, reflectionNumerator p s i j % (p : ℤ) ≠ 0 := by
    obtain ⟨i, hi⟩ := hsnz
    refine ⟨i, i, ?_⟩
    intro hz
    have he : (-(s i * s i) : ℤ) % (p : ℤ) = 0 := by
      simpa [reflectionNumerator, Int.sub_emod] using hz
    have hd : (p : ℤ) ∣ s i * s i := dvd_neg.mp (Int.dvd_of_emod_eq_zero he)
    exact hi (Int.emod_eq_zero_of_dvd (prime_cancel_nonzero_residue hp (s i) (s i) hi hd))
  have hvn : ∃ i, v i % (p : ℤ) ≠ 0 := by
    obtain ⟨i, hi⟩ := hsnz
    exact ⟨i, by rwa [← hsv]⟩
  refine ⟨reflectionMatrix p s, generated_implies_published hp v _ ?_⟩
  exact ⟨reflection_orthogonal hp0 s hnorm, reflection_regular s hsum,
    exactLevel_of_numerator_nonzero hp _ _ (reflection_numerator hp0 s) hnz,
    reflectionNumerator p s, reflection_numerator hp0 s, ⟨hnz, v, hvn, hline⟩, hline⟩

#print axioms balanced_reflection_exists
end Wang38I
