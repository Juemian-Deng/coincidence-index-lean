import NormTwoStar
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.Option

/-! Actual integer-matrix bridge for an already oriented equal-residue class.
The selected columns are indexed by Option ι: none is the base, some j are
at least four further columns. No normal form is an input. -/
namespace MatrixLargeClass
open IntegerNormTwo
open scoped BigOperators

variable {α ι β : Type*} [Fintype α] [DecidableEq α]

def column (P : α → β → ℤ) (j : β) : α → ℤ := fun x => P x j

def OrthogonalColumns [DecidableEq β] (P : α → β → ℤ) (d : ℤ) : Prop :=
  ∀ j k, dot (column P j) (column P k) = if j = k then d ^ 2 else 0

def differenceRoot (P : α → Option ι → ℤ) (d : ℤ) (j : ι) : α → ℤ :=
  fun x => (P x (some j) - P x none) / d

omit [DecidableEq α] in
theorem dot_comm (v w : α → ℤ) : dot v w = dot w v := by
  unfold dot
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [DecidableEq α] in
theorem dot_sub_sub (v w z : α → ℤ) :
    dot (fun x => v x - z x) (fun x => w x - z x) =
      dot v w - dot v z - dot z w + dot z z := by
  simp only [dot, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [DecidableEq α] in
theorem dot_scale (a b : ℤ) (v w : α → ℤ) :
    dot (fun x => a * v x) (fun x => b * w x) = a * b * dot v w := by
  unfold dot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [DecidableEq α] in
theorem normSq_eq_dot (v : α → ℤ) : normSq v = dot v v := by
  simp [normSq, dot, pow_two]

omit [Fintype α] [DecidableEq α] in
theorem differenceRoot_scale (P : α → Option ι → ℤ) (d : ℤ)
    (hcong : ∀ j x, d ∣ P x (some j) - P x none) (j : ι) :
    (fun x => d * differenceRoot P d j x) =
      fun x => P x (some j) - P x none := by
  funext x
  exact Int.mul_ediv_cancel' (hcong j x)

omit [DecidableEq α] in
theorem differenceRoot_dot [DecidableEq ι]
    (P : α → Option ι → ℤ) (d : ℤ) (hd : 0 < d)
    (ho : OrthogonalColumns P d)
    (hcong : ∀ j x, d ∣ P x (some j) - P x none) (j k : ι) :
    dot (differenceRoot P d j) (differenceRoot P d k) =
      if j = k then 2 else 1 := by
  unfold OrthogonalColumns at ho
  have hscale := dot_scale d d (differenceRoot P d j) (differenceRoot P d k)
  rw [differenceRoot_scale P d hcong j, differenceRoot_scale P d hcong k] at hscale
  have he := dot_sub_sub (column P (some j)) (column P (some k)) (column P none)
  change dot (fun x => P x (some j) - P x none)
    (fun x => P x (some k) - P x none) = _ at he
  rw [he] at hscale
  simp only [ho, Option.some.injEq, Option.some_ne_none, reduceCtorEq,
    ite_false, ite_true, sub_zero] at hscale
  have hd2 : 0 < d * d := mul_pos hd hd
  split_ifs at hscale ⊢ <;> nlinarith

omit [DecidableEq α] in
theorem differenceRoot_norm [DecidableEq ι]
    (P : α → Option ι → ℤ) (d : ℤ) (hd : 0 < d)
    (ho : OrthogonalColumns P d)
    (hcong : ∀ j x, d ∣ P x (some j) - P x none) (j : ι) :
    normSq (differenceRoot P d j) = 2 := by
  rw [normSq_eq_dot, differenceRoot_dot P d hd ho hcong]
  simp

/-- Main structural bridge: orthogonality and divisibility alone produce an
injective signed coordinate embedding and the common-vector column formula. -/
theorem oriented_class_signed_normal_form [Fintype ι] [DecidableEq ι]
    (P : α → Option ι → ℤ) (d : ℤ) (hd : 0 < d)
    (ho : OrthogonalColumns P d) (hfour : 4 ≤ Fintype.card ι)
    (hcong : ∀ j x, d ∣ P x (some j) - P x none) :
    ∃ L : α → ℤ, ∃ row : Option ι → α, ∃ σ : Option ι → ℤ,
      Function.Injective row ∧
      (∀ j, σ j = 1 ∨ σ j = -1) ∧
      ∀ j x, P x j = L x - d * σ j * unitVector (row j) x := by
  obtain ⟨r, ε, leaf, η, hε, hleaf, hstar⟩ :=
    NormTwoStar.signed_star_decomposition_of_norm_two
      (Finset.univ : Finset ι) (differenceRoot P d) (by simpa using hfour)
      (fun j _ => differenceRoot_norm P d hd ho hcong j)
      (fun j _ k _ hjk => by rw [differenceRoot_dot P d hd ho hcong]; simp [hjk])
  let l : ι → α := fun j => leaf ⟨j, Finset.mem_univ j⟩
  let a : ι → ℤ := fun j => η ⟨j, Finset.mem_univ j⟩
  have hl : Function.Injective l := by
    intro j k hjk
    have := hleaf hjk
    exact congrArg Subtype.val this
  have hrl : ∀ j, r ≠ l j := fun j => (hstar ⟨j, Finset.mem_univ j⟩).1
  have ha : ∀ j, a j = 1 ∨ a j = -1 := fun j => (hstar ⟨j, Finset.mem_univ j⟩).2.1
  have hu : ∀ j x, differenceRoot P d j x =
      ε * unitVector r x + a j * unitVector (l j) x := by
    intro j x
    exact congrFun (hstar ⟨j, Finset.mem_univ j⟩).2.2 x
  refine ⟨fun x => P x none + d * ε * unitVector r x,
    (fun j => j.elim r l), (fun j => j.elim ε (fun k => -a k)), ?_, ?_, ?_⟩
  · intro j k hjk
    cases j with
    | none =>
      cases k with
      | none => rfl
      | some k => exact ((hrl k) hjk).elim
    | some j =>
      cases k with
      | none => exact ((hrl j) hjk.symm).elim
      | some k => exact congrArg some (hl hjk)
  · intro j
    cases j with
    | none => exact hε
    | some j => rcases ha j with h | h <;> simp [h]
  · intro j x
    cases j with
    | none => simp
    | some j =>
      have hx := congrFun (differenceRoot_scale P d hcong j) x
      rw [hu] at hx
      dsimp
      nlinarith

/-- Restricting any integer matrix to any injectively indexed oriented class
supplies exactly the hypotheses of the structural theorem. -/
theorem selected_class_signed_normal_form [Fintype ι] [DecidableEq ι] [DecidableEq β]
    (P : α → β → ℤ) (d : ℤ) (hd : 0 < d)
    (ho : OrthogonalColumns P d) (c : Option ι → β) (hc : Function.Injective c)
    (hfour : 4 ≤ Fintype.card ι)
    (hcong : ∀ j x, d ∣ P x (c (some j)) - P x (c none)) :
    ∃ L : α → ℤ, ∃ row : Option ι → α, ∃ σ : Option ι → ℤ,
      Function.Injective row ∧
      (∀ j, σ j = 1 ∨ σ j = -1) ∧
      ∀ j x, P x (c j) = L x - d * σ j * unitVector (row j) x := by
  apply oriented_class_signed_normal_form (fun x j => P x (c j)) d hd _ hfour hcong
  intro j k
  change dot (column P (c j)) (column P (c k)) = _
  rw [ho]
  simp only [hc.eq_iff]

/- An injective signed coordinate embedding extends to one simultaneous row
sign transformation. The construction imposes no assumptions on other rows. -/
omit [Fintype α] [DecidableEq α] in
theorem extend_coordinate_signs (row : β → α) (hr : Function.Injective row)
    (σ : β → ℤ) (hσ : ∀ j, σ j = 1 ∨ σ j = -1) :
    ∃ τ : α → ℤ, (∀ x, τ x = 1 ∨ τ x = -1) ∧ ∀ j, τ (row j) = σ j := by
  classical
  let τ : α → ℤ := fun x => if h : ∃ j, row j = x then σ h.choose else 1
  refine ⟨τ, ?_, ?_⟩
  · intro x
    dsimp [τ]
    split_ifs with h
    · exact hσ h.choose
    · exact Or.inl rfl
  · intro j
    have h : ∃ k, row k = row j := ⟨j, rfl⟩
    dsimp [τ]
    rw [dite_eq_left h]
    congr 1
    exact hr h.choose_spec

/-- Unsigned normal form after a single actual row-sign transformation. -/
theorem oriented_class_normal_form [Fintype ι] [DecidableEq ι]
    (P : α → Option ι → ℤ) (d : ℤ) (hd : 0 < d)
    (ho : OrthogonalColumns P d) (hfour : 4 ≤ Fintype.card ι)
    (hcong : ∀ j x, d ∣ P x (some j) - P x none) :
    ∃ τ L : α → ℤ, ∃ row : Option ι → α,
      (∀ x, τ x = 1 ∨ τ x = -1) ∧ Function.Injective row ∧
      ∀ j x, τ x * P x j = L x - d * unitVector (row j) x := by
  obtain ⟨L, row, σ, hr, hσ, hp⟩ := oriented_class_signed_normal_form P d hd ho hfour hcong
  obtain ⟨τ, hτ, hτσ⟩ := extend_coordinate_signs row hr σ hσ
  refine ⟨τ, fun x => τ x * L x, row, hτ, hr, ?_⟩
  intro j x
  rw [hp]
  by_cases hx : x = row j
  · subst x
    simp only [hτσ]
    rcases hσ j with h | h
    · simp [h, unitVector]
    · simp [h, unitVector]
      ring
  · simp [unitVector, hx]

/- Row signs preserve the actual integer dot products. -/
omit [DecidableEq α] in
theorem row_signs_preserve_dot (τ v w : α → ℤ)
    (hτ : ∀ x, τ x = 1 ∨ τ x = -1) :
    dot (fun x => τ x * v x) (fun x => τ x * w x) = dot v w := by
  unfold dot
  apply Finset.sum_congr rfl
  intro x _
  rcases hτ x with h | h <;> simp [h]

end MatrixLargeClass
