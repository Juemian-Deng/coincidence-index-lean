import RationalResidueConnection
import Mathlib.LinearAlgebra.UnitaryGroup

namespace RationalResidueConnection
variable {n : ℕ}

/-- The positive-denominator data are constructed from actual Mathlib orthogonality. -/
theorem exists_orthogonal_integer_presentation (R : Matrix (Fin n) (Fin n) ℚ)
    (horth : R ∈ Matrix.orthogonalGroup (Fin n) ℚ) :
    ∃ d : ℕ, 0 < d ∧ ∃ P : Matrix (Fin n) (Fin n) ℤ,
      (∀ i j, (P i j : ℚ) = (d : ℚ) * R i j) ∧
      (∀ i j, R i j = (P i j : ℚ) / (d : ℚ)) ∧
      P.transpose * P = (d : ℤ)^2 • (1 : Matrix (Fin n) (Fin n) ℤ) ∧
      P * P.transpose = (d : ℤ)^2 • (1 : Matrix (Fin n) (Fin n) ℤ) ∧
      coincidenceSubgroup R = ResidueParityBridge.residueKernel P d := by
  refine ⟨commonDenominator R, commonDenominator_pos R, integerNumerator R,
    integerNumerator_cast R, integerNumerator_div R, ?_, ?_, ?_⟩
  · exact column_gram R _ _ (integerNumerator_cast R)
      ((Matrix.mem_orthogonalGroup_iff' (Fin n) ℚ).mp horth)
  · exact row_gram R _ _ (integerNumerator_cast R)
      ((Matrix.mem_orthogonalGroup_iff (Fin n) ℚ).mp horth)
  · exact coincidenceSubgroup_eq_residueKernel R _ _ (commonDenominator_pos R)
      (integerNumerator_cast R)

end RationalResidueConnection
