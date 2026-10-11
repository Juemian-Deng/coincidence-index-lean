import FixedSignCapacity
import ResidueParityBridge

/-! The fixed-class bound applied to labels in the actual image of P modulo d. -/
namespace FixedSignCapacity
open scoped BigOperators
variable {n : ℕ} (P : Matrix (Fin n) (Fin n) ℤ) (d : ℕ)

/-- The coordinate model and the residue-image subtype label agree exactly. -/
theorem columnLabel_val_eq_columnResidue (j : Fin n) :
    (ResidueParityBridge.columnLabel P d j).val = columnResidue P d j := by
  funext i
  exact ResidueParityBridge.columnLabel_apply P d i j

/-- A parity character excludes zero residue columns. -/
theorem columnResidue_ne_zero_of_even
    (heven : ResidueParityBridge.KernelEven P d) (j : Fin n) :
    columnResidue P d j ≠ 0 := by
  intro hz
  apply ResidueParityBridge.columnLabel_ne_zero P d heven j
  apply Subtype.ext
  simpa only [columnLabel_val_eq_columnResidue, AddSubgroup.coe_zero] using hz

/-- Even residue kernel plus an actual column Gram identity forces core strictness. -/
theorem gram_even_core (hd : 0 < d)
    (hcols : P.transpose * P = (d : ℤ) ^ 2 • (1 : Matrix (Fin n) (Fin n) ℤ))
    (heven : ResidueParityBridge.KernelEven P d) :
    ∀ i j, |P i j| < (d : ℤ) := by
  exact strict_core_of_nonzero_residue P d hd (column_norm_of_gram P d hcols)
    (columnResidue_ne_zero_of_even P d heven)

/-- The class defined inside the actual image subgroup equals the coordinate class. -/
theorem image_absoluteClass_eq (j₀ : Fin n) :
    (Finset.univ.filter (fun j =>
      ResidueParityBridge.columnLabel P d j = ResidueParityBridge.columnLabel P d j₀ ∨
      ResidueParityBridge.columnLabel P d j = -ResidueParityBridge.columnLabel P d j₀)) =
    absoluteClass P d j₀ := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, absoluteClass]
  constructor
  · rintro (h | h)
    · left
      simpa only [columnLabel_val_eq_columnResidue] using congrArg Subtype.val h
    · right
      simpa only [AddSubgroup.coe_neg, columnLabel_val_eq_columnResidue] using congrArg Subtype.val h
  · rintro (h | h)
    · left
      apply Subtype.ext
      simpa only [columnLabel_val_eq_columnResidue] using h
    · right
      apply Subtype.ext
      simpa only [AddSubgroup.coe_neg, columnLabel_val_eq_columnResidue] using h

/-- Capacity four for the actual fixed image label, with strictness derived.
Only positivity, actual row/column Gram identities, and the even kernel are inputs. -/
theorem gram_even_fixed_image_class_card_le_four (hd : 0 < d)
    (hrows : P * P.transpose = (d : ℤ) ^ 2 • (1 : Matrix (Fin n) (Fin n) ℤ))
    (hcols : P.transpose * P = (d : ℤ) ^ 2 • (1 : Matrix (Fin n) (Fin n) ℤ))
    (heven : ResidueParityBridge.KernelEven P d) (j₀ : Fin n)
    (hfixed : ResidueParityBridge.columnLabel P d j₀ =
      -ResidueParityBridge.columnLabel P d j₀) :
    (Finset.univ.filter (fun j =>
      ResidueParityBridge.columnLabel P d j = ResidueParityBridge.columnLabel P d j₀ ∨
      ResidueParityBridge.columnLabel P d j = -ResidueParityBridge.columnLabel P d j₀)).card ≤ 4 := by
  rw [image_absoluteClass_eq]
  apply gram_fixed_class_card_le_four P d hd hrows hcols (gram_even_core P d hd hcols heven)
  simpa only [AddSubgroup.coe_neg, columnLabel_val_eq_columnResidue] using congrArg Subtype.val hfixed

end FixedSignCapacity
