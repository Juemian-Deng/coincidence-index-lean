import FiniteClassRows
import FixedSignCapacity

set_option linter.unusedSectionVars false

namespace SignClassTransfer
open IntegerNormTwo MatrixLargeClass FixedSignCapacity
open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- Independently changing column signs preserves the full column Gram data. -/
theorem column_signs_preserve_orthogonality
    (P : α → β → ℤ) (d : ℤ) (σ : β → ℤ)
    (hσ : ∀ j, σ j = 1 ∨ σ j = -1) (ho : OrthogonalColumns P d) :
    OrthogonalColumns (fun x j => σ j * P x j) d := by
  intro j k
  change dot (fun x => σ j * column P j x) (fun x => σ k * column P k x) = _
  rw [dot_scale, ho]
  by_cases h : j = k
  · subst k
    rcases hσ j with hs | hs <;> simp [hs]
  · simp [h]

/-- Equality of actual residue columns up to one global sign can be oriented
simultaneously, including columns outside the selected set. -/
theorem orient_residue_class
    (P : α → β → ℤ) (d : ℕ) (J : Finset β) (g : α → ZMod d)
    (hc : ∀ j ∈ J, columnResidue P d j = g ∨ columnResidue P d j = -g) :
    ∃ σ : β → ℤ, (∀ j, σ j = 1 ∨ σ j = -1) ∧
      ∀ j ∈ J, columnResidue (fun x k => σ k * P x k) d j = g := by
  classical
  let σ : β → ℤ := fun j => if columnResidue P d j = g then 1 else -1
  refine ⟨σ, ?_, ?_⟩
  · intro j
    dsimp [σ]
    split_ifs <;> simp
  · intro j hj
    rcases hc j hj with h | h
    · ext x
      simpa [columnResidue, σ, h] using congrFun h x
    · by_cases he : columnResidue P d j = g
      · ext x
        simpa [columnResidue, σ, he] using congrFun he x
      · ext x
        have hx := congrFun h x
        change (P x j : ZMod d) = -g x at hx
        simp [columnResidue, σ, he, hx]

/-- Actual equality of residue columns is equivalent to divisibility of all
coordinate differences. -/
theorem residue_eq_iff_dvd (P : α → β → ℤ) (d : ℕ) (j k : β) :
    columnResidue P d j = columnResidue P d k ↔
      ∀ x, (d : ℤ) ∣ P x j - P x k := by
  constructor
  · intro h x
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp only [Int.cast_sub]
    exact sub_eq_zero.mpr (congrFun h x)
  · intro h
    ext x
    have hx := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (h x)
    simpa only [Int.cast_sub, sub_eq_zero, columnResidue] using hx

/-- A sign can be canceled from an integer divisibility relation. -/
theorem dvd_of_sign_mul (d a σ : ℤ) (hσ : σ = 1 ∨ σ = -1)
    (h : d ∣ σ * a) : d ∣ a := by
  rcases hσ with hσ | hσ
  · simpa [hσ] using h
  · simpa [hσ] using h

/-- The actual large sign class, with its orientation, signed normal form,
and full-row congruence. No normal-form or row-capacity hypothesis is used. -/
theorem finite_sign_class_row_containment
    (P : α → β → ℤ) (d : ℕ) (hd : 0 < d)
    (ho : OrthogonalColumns P (d : ℤ))
    (J : Finset β) (hfive : 5 ≤ J.card) (g : α → ZMod d)
    (hc : ∀ j ∈ J, columnResidue P d j = g ∨ columnResidue P d j = -g) :
    ∃ σ : β → ℤ, ∃ τ L : α → ℤ, ∃ row : J → α,
      (∀ j, σ j = 1 ∨ σ j = -1) ∧
      (∀ x, τ x = 1 ∨ τ x = -1) ∧ Function.Injective row ∧
      (∀ j : J, ∀ x, τ x * (σ j * P x j) =
        L x - (d : ℤ) * unitVector (row j) x) ∧
      ∀ j k : J, ∀ y,
        (d : ℤ) ∣ τ (row j) * P (row j) y - τ (row k) * P (row k) y := by
  obtain ⟨σ, hσ, hcσ⟩ := orient_residue_class P d J g hc
  let Q : α → β → ℤ := fun x j => σ j * P x j
  have hq : OrthogonalColumns Q (d : ℤ) :=
    column_signs_preserve_orthogonality P d σ hσ ho
  have hcong : ∀ j ∈ J, ∀ k ∈ J, ∀ x, (d : ℤ) ∣ Q x j - Q x k := by
    intro j hj k hk
    apply (residue_eq_iff_dvd Q d j k).mp
    exact (hcσ j hj).trans (hcσ k hk).symm
  obtain ⟨τ, L, row, hτ, hr, hp, he⟩ :=
    finite_oriented_class_row_containment Q d (by exact_mod_cast hd) hq J hfive hcong
  refine ⟨σ, τ, L, row, hσ, hτ, hr, hp, ?_⟩
  intro j k y
  apply dvd_of_sign_mul (d : ℤ) _ (σ y) (hσ y)
  convert he j k y using 1
  dsimp [Q]
  ring

/-- Cancel the two independent row signs to obtain one whole-row sign class. -/
theorem residue_same_sign_of_signed_dvd
    (a b : β → ℤ) (d : ℕ) (r s : ℤ)
    (hr : r = 1 ∨ r = -1) (hs : s = 1 ∨ s = -1)
    (h : ∀ y, (d : ℤ) ∣ r * a y - s * b y) :
    (fun y => (a y : ZMod d)) = (fun y => (b y : ZMod d)) ∨
    (fun y => (a y : ZMod d)) = -(fun y => (b y : ZMod d)) := by
  have he : ∀ y, (r : ZMod d) * (a y : ZMod d) = (s : ZMod d) * (b y : ZMod d) := by
    intro y
    have hy := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (h y)
    simpa only [Int.cast_sub, Int.cast_mul, sub_eq_zero] using hy
  rcases hr with hr | hr <;> rcases hs with hs | hs
  · left; ext y; simpa [hr, hs] using he y
  · right; ext y; simpa [hr, hs] using he y
  · right; ext y; simpa [hr, hs, neg_eq_iff_eq_neg] using he y
  · left; ext y; simpa [hr, hs] using he y

/-- Every actual sign class of at least five columns embeds into one actual
row sign class of the full matrix. -/
theorem absoluteClass_card_le_transpose_class
    (P : α → β → ℤ) (d : ℕ) (hd : 0 < d)
    (ho : OrthogonalColumns P (d : ℤ)) (j₀ : β)
    (hfive : 5 ≤ (absoluteClass P d j₀).card) :
    ∃ i₀ : α, (absoluteClass P d j₀).card ≤
      (absoluteClass (fun j i => P i j) d i₀).card := by
  classical
  let J := absoluteClass P d j₀
  obtain ⟨σ, τ, L, row, _, hτ, hr, _, hres⟩ :=
    finite_sign_class_row_containment P d hd ho J hfive (columnResidue P d j₀)
      (fun j hj => (Finset.mem_filter.mp hj).2)
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (show 0 < J.card by dsimp [J]; omega)
  let b' : J := ⟨b, hb⟩
  refine ⟨row b', ?_⟩
  have hsub : Finset.univ.image row ⊆ absoluteClass (fun j i => P i j) d (row b') := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact residue_same_sign_of_signed_dvd (fun y => P (row j) y)
      (fun y => P (row b') y) d (τ (row j)) (τ (row b'))
      (hτ _) (hτ _) (hres j b')
  calc
    J.card = (Finset.univ.image row).card := by
      rw [Finset.card_image_of_injective _ hr]
      simp
    _ ≤ _ := Finset.card_le_card hsub

/-- The concrete column Gram equation implies the dot-product interface. -/
theorem orthogonalColumns_of_gram
    (P : Matrix α β ℤ) (d : ℤ)
    (hg : P.transpose * P = d ^ 2 • (1 : Matrix β β ℤ)) :
    OrthogonalColumns P d := by
  intro j k
  have h := congrFun (congrFun hg j) k
  by_cases hjk : j = k
  · subst k
    simpa [dot, column, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.smul_apply] using h
  · simpa [dot, column, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.smul_apply, hjk] using h

/-- Transpose transfer bounds every actual row class by the supplied actual
column-class cap, with the sharp structural exception of size at most four. -/
theorem row_class_card_le_max_of_column_cap
    (P : Matrix α β ℤ) (d K : ℕ) (hd : 0 < d)
    (hrows : P * P.transpose = (d : ℤ) ^ 2 • (1 : Matrix α α ℤ))
    (hcap : ∀ j, (absoluteClass P d j).card ≤ K) (i : α) :
    (absoluteClass P.transpose d i).card ≤ max 4 K := by
  by_cases hsmall : (absoluteClass P.transpose d i).card ≤ 4
  · exact hsmall.trans (le_max_left _ _)
  · have hfive : 5 ≤ (absoluteClass P.transpose d i).card := by omega
    have ho : OrthogonalColumns P.transpose (d : ℤ) :=
      orthogonalColumns_of_gram P.transpose d (by simpa using hrows)
    obtain ⟨j, hj⟩ := absoluteClass_card_le_transpose_class P.transpose d hd ho i hfive
    exact hj.trans ((hcap j).trans (le_max_right _ _))

/-- When the maximum column class is at least four, there is no loss in the
transpose row-class cap. -/
theorem row_class_card_le_of_column_cap
    (P : Matrix α β ℤ) (d K : ℕ) (hd : 0 < d) (hK : 4 ≤ K)
    (hrows : P * P.transpose = (d : ℤ) ^ 2 • (1 : Matrix α α ℤ))
    (hcap : ∀ j, (absoluteClass P d j).card ≤ K) (i : α) :
    (absoluteClass P.transpose d i).card ≤ K := by
  simpa only [max_eq_right hK] using
    row_class_card_le_max_of_column_cap P d K hd hrows hcap i

def columnSigned (P : Matrix α β ℤ) (σ : β → ℤ) : Matrix α β ℤ :=
  fun x j => σ j * P x j

/-- The other Gram product is unchanged by arbitrary column signs. -/
theorem column_signs_preserve_row_product
    (P : Matrix α β ℤ) (σ : β → ℤ) (hσ : ∀ j, σ j = 1 ∨ σ j = -1) :
    columnSigned P σ * (columnSigned P σ).transpose =
      P * P.transpose := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, columnSigned]
  apply Finset.sum_congr rfl
  intro j _
  rcases hσ j with h | h <;> simp [h]

/-- The maximum is taken over actual full residue sign classes. -/
def maxClassSize (P : α → β → ℤ) (d : ℕ) : ℕ :=
  Finset.univ.sup (fun j => (absoluteClass P d j).card)

theorem class_card_le_max (P : α → β → ℤ) (d : ℕ) (j : β) :
    (absoluteClass P d j).card ≤ maxClassSize P d := by
  exact Finset.le_sup (f := fun k => (absoluteClass P d k).card) (Finset.mem_univ j)

/-- Literal maximum-row-class transfer, with no supplied class cap. -/
theorem max_row_class_le
    (P : Matrix α β ℤ) (d : ℕ) (hd : 0 < d)
    (hrows : P * P.transpose = (d : ℤ) ^ 2 • (1 : Matrix α α ℤ)) :
    maxClassSize P.transpose d ≤ max 4 (maxClassSize P d) := by
  apply Finset.sup_le
  intro i _
  exact row_class_card_le_max_of_column_cap P d (maxClassSize P d) hd hrows
    (class_card_le_max P d) i

/-- In the large-class range, the actual two maxima agree. -/
theorem max_classes_equal_of_large
    (P : Matrix α β ℤ) (d : ℕ) (hd : 0 < d)
    (hrows : P * P.transpose = (d : ℤ) ^ 2 • (1 : Matrix α α ℤ))
    (hcols : P.transpose * P = (d : ℤ) ^ 2 • (1 : Matrix β β ℤ))
    (hlarge : 5 ≤ maxClassSize P d) :
    maxClassSize P.transpose d = maxClassSize P d := by
  have h₁ := max_row_class_le P d hd hrows
  have h₂ := max_row_class_le P.transpose d hd (by simpa using hcols)
  change maxClassSize P d ≤ max 4 (maxClassSize P.transpose d) at h₂
  omega

/-- Nonzero actual residue input yields the positive own value and linear
class-size bound after global column orientation. -/
theorem finite_nonzero_sign_class_normal_form
    (P : α → β → ℤ) (d : ℕ) (hd : 0 < d)
    (ho : OrthogonalColumns P (d : ℤ))
    (J : Finset β) (hfive : 5 ≤ J.card) (g : α → ZMod d) (hg : g ≠ 0)
    (hc : ∀ j ∈ J, columnResidue P d j = g ∨ columnResidue P d j = -g) :
    ∃ σ : β → ℤ, ∃ τ L : α → ℤ, ∃ row : J → α, ∃ s : ℤ,
      (∀ j, σ j = 1 ∨ σ j = -1) ∧
      (∀ x, τ x = 1 ∨ τ x = -1) ∧ Function.Injective row ∧
      (∀ j : J, ∀ x, τ x * (σ j * P x j) =
        L x - (d : ℤ) * unitVector (row j) x) ∧
      0 < s ∧ s < d ∧ (∀ j, L (row j) = s) ∧
      normSq L = 2 * d * s ∧ (J.card : ℤ) * s ≤ 2 * d ∧
      ∀ j : J, columnResidue (fun y x => P x y) d (row j) ≠ 0 := by
  obtain ⟨σ, hσ, hcσ⟩ := orient_residue_class P d J g hc
  let Q : α → β → ℤ := fun x j => σ j * P x j
  have hq : OrthogonalColumns Q (d : ℤ) :=
    column_signs_preserve_orthogonality P d σ hσ ho
  have hcong : ∀ j ∈ J, ∀ k ∈ J, ∀ x, (d : ℤ) ∣ Q x j - Q x k := by
    intro j hj k hk
    apply (residue_eq_iff_dvd Q d j k).mp
    exact (hcσ j hj).trans (hcσ k hk).symm
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (show 0 < J.card by omega)
  obtain ⟨x, hx⟩ : ∃ x, g x ≠ 0 := by
    by_contra h
    push Not at h
    exact hg (funext h)
  have hn : ∃ j ∈ J, ∃ x, ¬(d : ℤ) ∣ Q x j := by
    refine ⟨b, hb, x, ?_⟩
    intro hdiv
    apply hx
    have he := congrFun (hcσ b hb) x
    change (Q x b : ZMod d) = g x at he
    exact he.symm.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdiv)
  obtain ⟨τ, L, row, s, hτ, hr, hp, hs, hv, he, hbound⟩ :=
    finite_oriented_nonzero_class_normal_form Q d (by exact_mod_cast hd) hq J hfive hcong hn
  have hfive' : (5 : ℤ) ≤ J.card := by exact_mod_cast hfive
  have hsd : s < d := by nlinarith
  refine ⟨σ, τ, L, row, s, hσ, hτ, hr, hp, hs, hsd, hv, he, hbound, ?_⟩
  intro j hz
  have hzj := congrFun hz j.val
  change (P (row j) j : ZMod d) = 0 at hzj
  have hdiv : (d : ℤ) ∣ P (row j) j :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzj
  have hdiv' : (d : ℤ) ∣ τ (row j) * Q (row j) j := by
    dsimp [Q]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hdiv _) _
  have hvalue := hp j (row j)
  rw [hv j] at hvalue
  simp only [unitVector] at hvalue
  rw [hvalue] at hdiv'
  have hds : (d : ℤ) ∣ s := by
    have := dvd_add hdiv' (dvd_refl (d : ℤ))
    simpa using this
  obtain ⟨q, hq⟩ := hds
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  have hqpos : 0 < q := by nlinarith
  have hqone : 1 ≤ q := by omega
  nlinarith

/-- Row and column signs do not change squared original entries. -/
theorem signed_entry_square (a r s : ℤ) (hr : r = 1 ∨ r = -1)
    (hs : s = 1 ∨ s = -1) : (r * (s * a)) ^ 2 = a ^ 2 := by
  rcases hr with hr | hr <;> rcases hs with hs | hs <;> simp [hr, hs]

/-- The exact off-block energy in the original matrix, removing all sign
normalizations. This applies to the normal form produced above. -/
theorem original_outside_block_energy
    (P : α → β → ℤ) (d s : ℤ) (ho : OrthogonalColumns P d)
    (J : Finset β) (σ : β → ℤ) (τ L : α → ℤ) (row : J → α)
    (hσ : ∀ j, σ j = 1 ∨ σ j = -1)
    (hτ : ∀ x, τ x = 1 ∨ τ x = -1) (hr : Function.Injective row)
    (hs : ∀ j, L (row j) = s)
    (hp : ∀ j : J, ∀ x, τ x * (σ j * P x j) =
      L x - d * unitVector (row j) x) (j : J) :
    (∑ x ∈ Finset.univ \ Finset.univ.image row, P x j ^ 2) =
      2 * d * s - (J.card : ℤ) * s ^ 2 := by
  let Q : α → J → ℤ := fun x k => τ x * (σ k * P x k)
  have hn : normSq (column Q j) = d ^ 2 := by
    have he : normSq (column Q j) = normSq (column P j) := by
      unfold normSq
      apply Finset.sum_congr rfl
      intro x _
      exact signed_entry_square (P x j) (τ x) (σ j) (hτ x) (hσ j)
    rw [he, normSq_eq_dot, ho]
    simp
  have he := outside_block_energy Q d s j L row hr hs hp hn
  have hsum : (∑ x ∈ Finset.univ \ Finset.univ.image row, Q x j ^ 2) =
      ∑ x ∈ Finset.univ \ Finset.univ.image row, P x j ^ 2 := by
    apply Finset.sum_congr rfl
    intro x _
    exact signed_entry_square (P x j) (τ x) (σ j) (hτ x) (hσ j)
  rw [hsum] at he
  simpa only [Fintype.card_coe] using he

end SignClassTransfer
