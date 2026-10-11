import FiniteClassBridge

namespace MatrixLargeClass
open IntegerNormTwo
open scoped BigOperators
variable {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]

theorem dot_sub_coordinate (v L : α → ℤ) (d : ℤ) (r : α) :
    dot v (fun x => L x - d * unitVector r x) = dot v L - d * v r := by
  unfold dot
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  simp [unitVector, mul_ite, mul_comm]

/-- Orthogonality forces every external column to be constant on the own
rows after the same simultaneous row-sign transformation. -/
theorem external_column_constant
    (P : α → β → ℤ) (d : ℤ) (hd : 0 < d) (ho : OrthogonalColumns P d)
    (J : Finset β) (τ L : α → ℤ) (row : J → α)
    (hτ : ∀ x, τ x = 1 ∨ τ x = -1)
    (hp : ∀ j : J, ∀ x, τ x * P x j = L x - d * unitVector (row j) x)
    (y : β) (hy : y ∉ J) (j k : J) :
    τ (row j) * P (row j) y = τ (row k) * P (row k) y := by
  have he : ∀ q : J, dot (fun x => τ x * P x y) L -
      d * (τ (row q) * P (row q) y) = 0 := by
    intro q
    have hqy : y ≠ q.val := by intro h; apply hy; rw [h]; exact q.property
    have h := ho y q
    have hv := row_signs_preserve_dot τ (column P y) (column P q) hτ
    have hform : (fun x => τ x * column P q x) =
        (fun x => L x - d * unitVector (row q) x) := by funext x; exact hp q x
    rw [hform, dot_sub_coordinate, h] at hv
    simpa only [column, ite_eq_right hqy] using hv
  have hj := he j
  have hk := he k
  nlinarith

/-- The embedded own rows belong to one actual row sign class of the full
matrix, since all their signed entry differences are divisible by d. -/
theorem own_rows_equal_residue
    (P : α → β → ℤ) (d s : ℤ) (hd : 0 < d) (ho : OrthogonalColumns P d)
    (J : Finset β) (τ L : α → ℤ) (row : J → α)
    (hτ : ∀ x, τ x = 1 ∨ τ x = -1)
    (hp : ∀ j : J, ∀ x, τ x * P x j = L x - d * unitVector (row j) x)
    (hs : ∀ j, L (row j) = s) :
    ∀ j k : J, ∀ y, d ∣ τ (row j) * P (row j) y - τ (row k) * P (row k) y := by
  intro j k y
  by_cases hy : y ∈ J
  · rw [hp ⟨y, hy⟩, hp ⟨y, hy⟩, hs, hs]
    exact ⟨unitVector (row ⟨y, hy⟩) (row k) - unitVector (row ⟨y, hy⟩) (row j), by ring⟩
  · rw [external_column_constant P d hd ho J τ L row hτ hp y hy j k]
    simp

/-- Fully derived row-class containment, with the injective row embedding
and signed normal form included. No normal form is assumed. -/
theorem finite_oriented_class_row_containment
    (P : α → β → ℤ) (d : ℤ) (hd : 0 < d) (ho : OrthogonalColumns P d)
    (J : Finset β) (hfive : 5 ≤ J.card)
    (hcong : ∀ j ∈ J, ∀ k ∈ J, ∀ x, d ∣ P x j - P x k) :
    ∃ τ L : α → ℤ, ∃ row : J → α,
      (∀ x, τ x = 1 ∨ τ x = -1) ∧ Function.Injective row ∧
      (∀ j : J, ∀ x, τ x * P x j = L x - d * unitVector (row j) x) ∧
      ∀ j k : J, ∀ y, d ∣ τ (row j) * P (row j) y - τ (row k) * P (row k) y := by
  obtain ⟨τ, L, row, s, hτ, hr, hp, _, hs, _, _, _⟩ :=
    finite_oriented_class_normal_form_energy P d hd ho J hfive hcong
  exact ⟨τ, L, row, hτ, hr, hp, own_rows_equal_residue P d s hd ho J τ L row hτ hp hs⟩

end MatrixLargeClass
