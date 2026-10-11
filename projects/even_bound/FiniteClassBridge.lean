import OwnBlockEnergy

/-! Finset-selected, arbitrary-matrix interface. All output data are derived
from the given matrix, column orthogonality, cardinality, and divisibility. -/
namespace MatrixLargeClass
open IntegerNormTwo
open scoped BigOperators
variable {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]

/-- Any actual oriented equal-residue class of at least five columns has the
normal form, constant own entries and exact common-vector energy. -/
theorem finite_oriented_class_normal_form_energy
    (P : α → β → ℤ) (d : ℤ) (hd : 0 < d) (ho : OrthogonalColumns P d)
    (J : Finset β) (hfive : 5 ≤ J.card)
    (hcong : ∀ j ∈ J, ∀ k ∈ J, ∀ x, d ∣ P x j - P x k) :
    ∃ τ L : α → ℤ, ∃ row : J → α, ∃ s : ℤ,
      (∀ x, τ x = 1 ∨ τ x = -1) ∧ Function.Injective row ∧
      (∀ j : J, ∀ x, τ x * P x j = L x - d * unitVector (row j) x) ∧
      0 ≤ s ∧ (∀ j, L (row j) = s) ∧ normSq L = 2 * d * s ∧
      (J.card : ℤ) * s ^ 2 ≤ 2 * d * s ∧
      ∀ j : J, (∑ x ∈ Finset.univ \ Finset.univ.image row, (τ x * P x j) ^ 2) =
        2 * d * s - (J.card : ℤ) * s ^ 2 := by
  classical
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (show 0 < J.card by omega)
  let I := J.erase b
  let c : Option I → β := fun j => j.elim b Subtype.val
  have hc : Function.Injective c := by
    intro j k hjk
    cases j with
    | none =>
      cases k with
      | none => rfl
      | some k => exact ((Finset.mem_erase.mp k.property).1 hjk.symm).elim
    | some j =>
      cases k with
      | none => exact ((Finset.mem_erase.mp j.property).1 hjk).elim
      | some k => exact congrArg some (Subtype.ext hjk)
  have hfour : 4 ≤ Fintype.card I := by
    simp only [Fintype.card_coe, I, Finset.card_erase_of_mem hb]
    omega
  have ho' : OrthogonalColumns (fun x j => P x (c j)) d := by
    intro j k
    change dot (column P (c j)) (column P (c k)) = _
    rw [ho]
    simp only [hc.eq_iff]
  have hcong' : ∀ j : I, ∀ x, d ∣ P x (c (some j)) - P x (c none) := by
    intro j x
    exact hcong j (Finset.mem_erase.mp j.property).2 b hb x
  obtain ⟨τ, L, r, s, hτ, hr, hp, hs0, hs, he, _, _⟩ :=
    oriented_class_normal_form_energy (fun x j => P x (c j)) d hd ho' hfour hcong'
  let t : J → Option I := fun j => if h : j.val = b then none else
    some ⟨j.val, Finset.mem_erase.mpr ⟨h, j.property⟩⟩
  have ht : ∀ j : J, c (t j) = j.val := by
    intro j
    dsimp [t]
    split_ifs with h
    · exact h.symm
    · rfl
  have hti : Function.Injective t := by
    intro j k hjk
    apply Subtype.ext
    rw [← ht j, ← ht k, hjk]
  let row : J → α := fun j => r (t j)
  have hrow : Function.Injective row := hr.comp hti
  have hform : ∀ j : J, ∀ x, τ x * P x j = L x - d * unitVector (row j) x := by
    intro j x
    have h := hp (t j) x
    simpa only [ht] using h
  have hs' : ∀ j : J, L (row j) = s := fun j => hs (t j)
  have hn : ∀ j : J, normSq (column (fun x (k : J) => τ x * P x k) j) = d ^ 2 := by
    intro j
    rw [normSq_eq_dot]
    change dot (fun x => τ x * P x j) (fun x => τ x * P x j) = _
    rw [row_signs_preserve_dot τ _ _ hτ]
    have h := ho j j
    change dot (fun x => P x j) (fun x => P x j) = if j.val = j.val then d ^ 2 else 0 at h
    simpa using h
  refine ⟨τ, L, row, s, hτ, hrow, hform, hs0, hs', he, ?_, ?_⟩
  · have h := own_block_energy_bound L row hrow s hs'
    simpa only [Fintype.card_coe, he] using h
  · intro j
    have h := outside_block_energy (fun x (k : J) => τ x * P x k) d s j L row hrow hs' hform (hn j)
    simpa only [Fintype.card_coe] using h

/-- For a nonzero residue class the own value is a positive integer and the
linear class-size bound follows from the derived energy inequality. -/
theorem finite_oriented_nonzero_class_normal_form
    (P : α → β → ℤ) (d : ℤ) (hd : 0 < d) (ho : OrthogonalColumns P d)
    (J : Finset β) (hfive : 5 ≤ J.card)
    (hcong : ∀ j ∈ J, ∀ k ∈ J, ∀ x, d ∣ P x j - P x k)
    (hnonzero : ∃ j ∈ J, ∃ x, ¬d ∣ P x j) :
    ∃ τ L : α → ℤ, ∃ row : J → α, ∃ s : ℤ,
      (∀ x, τ x = 1 ∨ τ x = -1) ∧ Function.Injective row ∧
      (∀ j : J, ∀ x, τ x * P x j = L x - d * unitVector (row j) x) ∧
      0 < s ∧ (∀ j, L (row j) = s) ∧ normSq L = 2 * d * s ∧
      (J.card : ℤ) * s ≤ 2 * d := by
  obtain ⟨τ, L, row, s, hτ, hr, hp, hs0, hs, he, hb, _⟩ :=
    finite_oriented_class_normal_form_energy P d hd ho J hfive hcong
  obtain ⟨j, hj, hx⟩ := hnonzero
  have hpos := own_value_pos_of_nonzero_residue (fun x (k : J) => P x k)
    d s τ L row hτ hp hs0 he ⟨j, hj⟩ hx
  exact ⟨τ, L, row, s, hτ, hr, hp, hpos, hs, he,
    own_value_linear_bound J.card d s hpos hb⟩

end MatrixLargeClass
