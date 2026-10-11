import ActualFiberBounds
import SignClassTransfer
import ResidueImageAdapter

namespace MatrixClassAdapters
open ResidueParityBridge ActualFiberBounds FixedSignCapacity SignClassTransfer

variable {n : ℕ} (P : Matrix (Fin n) (Fin n) ℤ) (d : ℕ)

/-- Actual-image column classes and coordinate residue classes are identical. -/
theorem column_class_eq (j : Fin n) :
    signClass (columnLabel P d) j = absoluteClass P d j := by
  classical
  ext k
  simp only [signClass, absoluteClass, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [columnLabel_eq_iff, columnLabel_eq_neg_iff]
  simp only [columnResidue, funext_iff, Pi.neg_apply]

/-- Actual character row classes and transposed residue column classes coincide. -/
theorem row_class_eq (i : Fin n) :
    signClass (rowEvaluation P d) i = absoluteClass P.transpose d i := by
  classical
  ext k
  simp only [signClass, absoluteClass, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [rowEvaluation_eq_iff, rowEvaluation_eq_neg_iff]
  simp only [columnResidue, Matrix.transpose_apply, funext_iff, Pi.neg_apply]

/-- Gram-derived maximum-column capacity bounds the actual row functionals. -/
theorem row_evaluation_class_card_le (K : ℕ) (hd : 0 < d) (hK : 4 ≤ K)
    (hrows : P * P.transpose = (d : ℤ)^2 • (1 : Matrix (Fin n) (Fin n) ℤ))
    (hcap : ∀ j, (signClass (columnLabel P d) j).card ≤ K) (i : Fin n) :
    (signClass (rowEvaluation P d) i).card ≤ K := by
  rw [row_class_eq]
  apply row_class_card_le_of_column_cap P d K hd hK hrows
  intro j
  simpa only [column_class_eq] using hcap j

end MatrixClassAdapters
