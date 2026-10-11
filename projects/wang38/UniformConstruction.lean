import FrameExtraction

/-! An unconditional, nonvacuous infinite-prime existence family: n=p and
the generating residue vector is constant and nonzero. This is a genuine
subcase of the target for p=3,5,7, not a classification assumption. -/
open scoped BigOperators
namespace Wang38I
open Wang38

/-- The rational Householder-type matrix 2J/p - I. -/
def uniformMatrix (p : ℕ) : QMatrix p := fun i j =>
  (2 : ℚ) / p - if i = j then 1 else 0

def uniformNumerator (p : ℕ) : IMatrix p := fun i j =>
  2 - (p : ℤ) * if i = j then 1 else 0

lemma uniform_orthogonal {p : ℕ} (hp : p ≠ 0) : Orthogonal (uniformMatrix p) := by
  classical
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  intro i j
  simp only [sumQ, List.sum_ofFn, uniformMatrix]
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
  simp only [mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp [eq_comm]
  split_ifs <;> field_simp <;> ring

lemma uniform_regular {p : ℕ} (hp : p ≠ 0) : Regular (uniformMatrix p) := by
  classical
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  intro i
  simp [sumQ, List.sum_ofFn, uniformMatrix, Finset.sum_sub_distrib]
  field_simp
  ring

lemma uniform_numerator {p : ℕ} (hp : p ≠ 0) :
    Numerator p (uniformMatrix p) (uniformNumerator p) := by
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  intro i j
  simp only [uniformNumerator, uniformMatrix]
  split_ifs <;> push_cast <;> field_simp

lemma uniform_numerator_mod {p : ℕ} (i j : Fin p) :
    uniformNumerator p i j % (p : ℤ) = 2 % (p : ℤ) := by
  unfold uniformNumerator
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]

/-- Exact original existence conclusion, for arbitrary odd prime p, when
n=p and all coordinates have the same nonzero residue. -/
theorem uniform_residue_exists {p : ℕ} (hp : OddPrime p) (v : IVector p)
    (a : ℤ) (ha : a % (p : ℤ) ≠ 0)
    (hv : ∀ i, v i % (p : ℤ) = a % (p : ℤ)) :
    ∃ Q : QMatrix p, PublishedGeneratedPrimitive p v Q := by
  classical
  let : Fact (Nat.Prime p) := ⟨oddPrime_isPrime hp⟩
  have hp3 := oddPrime_ge_three hp
  have hp0 : p ≠ 0 := by omega
  have htwo : (2 : ℤ) % (p : ℤ) ≠ 0 := by
    rw [Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ 2) (by omega : (2 : ℤ) < p)]
    decide
  have haZ : (a : ZMod p) ≠ 0 := by
    exact fun h => ha ((intCast_mod_zero_iff p _).mp h)
  let c : ℤ := ((2 : ZMod p) / (a : ZMod p)).val
  have hc : (c : ZMod p) = (2 : ZMod p) / (a : ZMod p) := by simp [c]
  have hline : ColumnsInLine p v (uniformNumerator p) := by
    intro j
    refine ⟨c, ?_⟩
    intro i
    rw [uniform_numerator_mod]
    apply (ZMod.intCast_eq_intCast_iff' _ _ p).mp
    have hvi : (v i : ZMod p) = (a : ZMod p) :=
      (ZMod.intCast_eq_intCast_iff' _ _ p).mpr (hv i)
    push_cast
    rw [hc, hvi, div_mul_cancel₀ _ haZ]
  have hnz : ∃ i j, uniformNumerator p i j % (p : ℤ) ≠ 0 := by
    refine ⟨⟨0, by omega⟩, ⟨0, by omega⟩, ?_⟩
    rwa [uniform_numerator_mod]
  refine ⟨uniformMatrix p, generated_implies_published hp v (uniformMatrix p) ?_⟩
  refine ⟨uniform_orthogonal hp0, uniform_regular hp0,
    exactLevel_of_numerator_nonzero hp _ _ (uniform_numerator hp0) hnz,
    uniformNumerator p, uniform_numerator hp0, ?_, hline⟩
  refine ⟨hnz, v, ?_, hline⟩
  exact ⟨⟨0, by omega⟩, by rw [hv]; exact ha⟩

/-- The companion explicit family in dimension 2p, using J/p - I. -/
theorem double_uniform_residue_exists {p : ℕ} (hp : OddPrime p) (v : IVector (2*p))
    (a : ℤ) (ha : a % (p : ℤ) ≠ 0)
    (hv : ∀ i, v i % (p : ℤ) = a % (p : ℤ)) :
    ∃ Q : QMatrix (2*p), PublishedGeneratedPrimitive p v Q := by
  classical
  let : Fact (Nat.Prime p) := ⟨oddPrime_isPrime hp⟩
  have hp3 := oddPrime_ge_three hp
  have hp0 : p ≠ 0 := by omega
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp0
  let Q := uniformMatrix (2*p)
  let A : IMatrix (2*p) := fun i j => 1 - (p : ℤ) * if i = j then 1 else 0
  have hn : Numerator p Q A := by
    intro i j
    dsimp [Q, A, uniformMatrix]
    split_ifs <;> push_cast <;> field_simp
  have hm : ∀ i j, A i j % (p : ℤ) = 1 % (p : ℤ) := by
    intro i j
    dsimp [A]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij]
  have haZ : (a : ZMod p) ≠ 0 := by
    exact fun h => ha ((intCast_mod_zero_iff p _).mp h)
  let c : ℤ := ((a : ZMod p)⁻¹).val
  have hc : (c : ZMod p) = (a : ZMod p)⁻¹ := by simp [c]
  have hline : ColumnsInLine p v A := by
    intro j
    refine ⟨c, ?_⟩
    intro i
    rw [hm]
    apply (ZMod.intCast_eq_intCast_iff' _ _ p).mp
    have hvi : (v i : ZMod p) = (a : ZMod p) :=
      (ZMod.intCast_eq_intCast_iff' _ _ p).mpr (hv i)
    push_cast
    rw [hc, hvi, inv_mul_cancel₀ haZ]
  have hnz : ∃ i j, A i j % (p : ℤ) ≠ 0 := by
    refine ⟨⟨0, by omega⟩, ⟨0, by omega⟩, ?_⟩
    rw [hm, Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ 1) (by omega : (1 : ℤ) < p)]
    decide
  refine ⟨Q, generated_implies_published hp v Q ?_⟩
  refine ⟨uniform_orthogonal (by omega), uniform_regular (by omega),
    exactLevel_of_numerator_nonzero hp Q A hn hnz, A, hn, ?_, hline⟩
  refine ⟨hnz, v, ?_, hline⟩
  exact ⟨⟨0, by omega⟩, by rw [hv]; exact ha⟩

#print axioms uniform_residue_exists
#print axioms double_uniform_residue_exists
end Wang38I
