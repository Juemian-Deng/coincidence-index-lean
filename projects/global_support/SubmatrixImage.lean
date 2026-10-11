import GeneralCoreBound

/-!
# Residue-image cardinality under passage to a square submatrix

A column combination for the selected matrix lifts to the same combination of
columns of the full matrix. Restricting the lifted vector to the selected rows
recovers the original image element. Thus the selected image injects into the
full image, without any hypothesis on the omitted rows or columns.
-/

namespace SubmatrixImage
open scoped BigOperators
open ResidueParityBridge

variable {n k : ℕ}

/-- Lift a coefficient vector for the selected columns to the full residue image. -/
def liftColumnCombination (P : Matrix (Fin n) (Fin n) ℤ) (d : ℕ)
    (col : Fin k → Fin n) (x : Fin k → ℤ) : ResidueImage P d :=
  ∑ b, x b • columnLabel P d (col b)

theorem liftColumnCombination_apply (P : Matrix (Fin n) (Fin n) ℤ) (d : ℕ)
    (row col : Fin k → Fin n) (x : Fin k → ℤ) (a : Fin k) :
    (liftColumnCombination P d col x).val (row a) =
      (imageMap (P.submatrix row col) d x).val a := by
  change _ = ((P.submatrix row col).mulVec x a : ZMod d)
  simp [liftColumnCombination, Matrix.mulVec, dotProduct,
    columnLabel_apply, Matrix.submatrix, zsmul_eq_mul, mul_comm]

/-- Choose an integer coefficient vector for an element of a residue image. -/
noncomputable def imageCoefficients (Q : Matrix (Fin k) (Fin k) ℤ) (d : ℕ)
    (v : ResidueImage Q d) : Fin k → ℤ :=
  Classical.choose ((residueMap Q d).rangeRestrict_surjective v)

theorem imageMap_imageCoefficients (Q : Matrix (Fin k) (Fin k) ℤ) (d : ℕ)
    (v : ResidueImage Q d) : imageMap Q d (imageCoefficients Q d v) = v :=
  Classical.choose_spec ((residueMap Q d).rangeRestrict_surjective v)

/-- A chosen set-theoretic lift of the selected residue image into the full image. -/
noncomputable def imageLift (P : Matrix (Fin n) (Fin n) ℤ) (d : ℕ)
    (row col : Fin k → Fin n) : ResidueImage (P.submatrix row col) d → ResidueImage P d :=
  fun v => liftColumnCombination P d col (imageCoefficients (P.submatrix row col) d v)

theorem imageLift_apply (P : Matrix (Fin n) (Fin n) ℤ) (d : ℕ)
    (row col : Fin k → Fin n) (v : ResidueImage (P.submatrix row col) d) (a : Fin k) :
    (imageLift P d row col v).val (row a) = v.val a := by
  unfold imageLift
  rw [liftColumnCombination_apply, imageMap_imageCoefficients]

theorem imageLift_injective (P : Matrix (Fin n) (Fin n) ℤ) (d : ℕ)
    (row col : Fin k → Fin n) : Function.Injective (imageLift P d row col) := by
  intro v w h
  apply Subtype.ext
  funext a
  have he := congrArg (fun z : ResidueImage P d => z.val (row a)) h
  simpa only [imageLift_apply] using he

/-- Selecting rows and columns never increases the cardinality of the residue
image. The index maps need not even be injective. -/
theorem card_residueImage_submatrix_le (P : Matrix (Fin n) (Fin n) ℤ) (d : ℕ)
    (hd : 0 < d) (row col : Fin k → Fin n) :
    Nat.card (ResidueImage (P.submatrix row col) d) ≤ Nat.card (ResidueImage P d) := by
  let : NeZero d := ⟨by omega⟩
  exact Nat.card_le_card_of_injective (imageLift P d row col) (imageLift_injective P d row col)

end SubmatrixImage

