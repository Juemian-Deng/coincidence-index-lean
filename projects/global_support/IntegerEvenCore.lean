import ResidueParityBridge
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Consequences of actual integer Gram identities and actual residue-kernel evenness. -/
namespace IntegerEvenCore
open scoped BigOperators
variable {n : ℕ} (P : Matrix (Fin n) (Fin n) ℤ) (d : ℕ)

/-- Evenness excludes zero residue rows, directly in the integer-numerator model. -/
theorem rowEvaluation_ne_zero (hd : 0 < d)
    (hgram : P * P.transpose = (d : ℤ)^2 • (1 : Matrix (Fin n) (Fin n) ℤ))
    (heven : ResidueParityBridge.KernelEven P d) (i : Fin n) :
    ResidueParityBridge.rowEvaluation P d i ≠ 0 := by
  intro hz
  have hdiv : ∀ j, (d : ℤ) ∣ P i j := by
    intro j
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      ((ResidueParityBridge.rowEvaluation_eq_zero_iff P d i).mp hz j)
  choose y hy using hdiv
  have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  have hd2 : (d : ℤ)^2 ≠ 0 := pow_ne_zero 2 hd0
  have hr (k l : Fin n) : ∑ j, P k j * P l j = if k = l then (d : ℤ)^2 else 0 := by
    have h := congrFun (congrFun hgram k) l
    simpa [Matrix.mul_apply, Matrix.one_apply] using h
  have hnorm : ∑ j, (y j)^2 = 1 := by
    apply mul_left_cancel₀ hd2
    calc
      (d : ℤ)^2 * ∑ j, (y j)^2 = ∑ j, P i j * P i j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [hy j]
        ring
      _ = (d : ℤ)^2 * 1 := by simpa using hr i i
  have hyker : ∀ k, (d : ℤ) ∣ P.mulVec y k := by
    intro k
    refine ⟨(if k = i then 1 else 0 : ℤ), ?_⟩
    apply mul_left_cancel₀ hd0
    calc
      (d : ℤ) * P.mulVec y k = ∑ j, P k j * P i j := by
        simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [hy j]
        ring
      _ = (d : ℤ) * ((d : ℤ) * if k = i then 1 else 0) := by
        rw [hr]
        split_ifs <;> simp [pow_two]
  have hpar := ZMod.intCast_eq_zero_iff_even.mpr (heven y hyker)
  rw [← ResidueParityBridge.norm_sum_parity, hnorm] at hpar
  norm_num at hpar

end IntegerEvenCore
