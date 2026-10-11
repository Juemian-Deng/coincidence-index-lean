import MatrixLargeClass

/-! Constancy and energy of the actual own block. These intermediate lemmas
accept a displayed normal form; the final theorem obtains that form directly
from orthogonality and equal residues via MatrixLargeClass. -/
namespace MatrixLargeClass
open IntegerNormTwo
open scoped BigOperators
variable {α β ι : Type*} [Fintype α] [DecidableEq α]

theorem normSq_sub_coordinate (L : α → ℤ) (d : ℤ) (r : α) :
    normSq (fun x => L x - d * unitVector r x) =
      normSq L - 2 * d * L r + d ^ 2 := by
  unfold normSq
  have hterm : ∀ x, (L x - d * unitVector r x) ^ 2 =
      L x ^ 2 - 2 * d * (if x = r then L x else 0) +
        (if x = r then d ^ 2 else 0) := by
    intro x
    by_cases hx : x = r
    · simp [unitVector, hx]
      ring
    · simp [unitVector, hx]
  simp_rw [hterm]
  simp [Finset.sum_sub_distrib, Finset.sum_add_distrib ]

omit [DecidableEq α] in
theorem normSq_nonneg (v : α → ℤ) : 0 ≤ normSq v := by
  exact Finset.sum_nonneg (fun x _ => sq_nonneg (v x))

/-- The displayed own rows all have one integer value, and their common
vector has exact energy 2*d*s. Positivity of s requires a core hypothesis. -/
theorem own_entries_and_energy [Nonempty β]
    (P : α → β → ℤ) (d : ℤ) (hd : 0 < d)
    (hnorm : ∀ j, normSq (column P j) = d ^ 2)
    (L : α → ℤ) (row : β → α)
    (hp : ∀ j x, P x j = L x - d * unitVector (row j) x) :
    ∃ s : ℤ, 0 ≤ s ∧ (∀ j, L (row j) = s) ∧ normSq L = 2 * d * s := by
  classical
  let j₀ : β := Classical.choice inferInstance
  have he : ∀ j, normSq L = 2 * d * L (row j) := by
    intro j
    have hcol : column P j = fun x => L x - d * unitVector (row j) x := by
      funext x
      exact hp j x
    have h := hnorm j
    rw [hcol, normSq_sub_coordinate] at h
    linarith
  refine ⟨L (row j₀), ?_, ?_, he j₀⟩
  · have := normSq_nonneg L
    rw [he j₀] at this
    nlinarith
  · intro j
    have h := he j
    have h₀ := he j₀
    nlinarith

/-- The sum of squared own entries is bounded by the actual common-vector
energy. The injective embedding prevents counting any row twice. -/
theorem own_block_energy_bound [Fintype β]
    (L : α → ℤ) (row : β → α) (hr : Function.Injective row)
    (s : ℤ) (hs : ∀ j, L (row j) = s) :
    (Fintype.card β : ℤ) * s ^ 2 ≤ normSq L := by
  classical
  have he : (∑ x ∈ Finset.univ.image row, L x ^ 2) =
      (Fintype.card β : ℤ) * s ^ 2 := by
    rw [Finset.sum_image (fun i _ j _ h => hr h)]
    simp [hs]
  rw [← he]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun x _ _ => sq_nonneg (L x))

/-- Exact outside energy after deleting the entire injective own block. -/
theorem outside_block_energy [Fintype β]
    (P : α → β → ℤ) (d s : ℤ) (j : β)
    (L : α → ℤ) (row : β → α) (hr : Function.Injective row)
    (hs : ∀ k, L (row k) = s)
    (hp : ∀ k x, P x k = L x - d * unitVector (row k) x)
    (hnorm : normSq (column P j) = d ^ 2) :
    (∑ x ∈ Finset.univ \ Finset.univ.image row, P x j ^ 2) =
      2 * d * s - (Fintype.card β : ℤ) * s ^ 2 := by
  classical
  have hown : (∑ x ∈ Finset.univ.image row, P x j ^ 2) =
      (Fintype.card β : ℤ) * s ^ 2 - 2 * d * s + d ^ 2 := by
    rw [Finset.sum_image (fun i _ k _ h => hr h)]
    have hterm : ∀ k, P (row k) j ^ 2 = s ^ 2 +
        if k = j then d ^ 2 - 2 * d * s else 0 := by
      intro k
      rw [hp, hs]
      by_cases hk : k = j
      · simp [unitVector, hk]
        ring
      · simp [unitVector, hr.ne hk, hk]
    simp_rw [hterm]
    simp [Finset.sum_add_distrib]
    ring
  have hsum := Finset.sum_sdiff (s₁ := Finset.univ.image row)
    (s₂ := (Finset.univ : Finset α)) (f := fun x => P x j ^ 2) (Finset.subset_univ _)
  have htotal : (∑ x : α, P x j ^ 2) = d ^ 2 := hnorm
  rw [htotal, hown] at hsum
  linarith

/-- End-to-end result: actual equal-residue orthogonal columns produce one
row-sign normalization, constant own entries, exact energy, and a block bound. -/
theorem oriented_class_normal_form_energy [Fintype ι] [DecidableEq ι]
    (P : α → Option ι → ℤ) (d : ℤ) (hd : 0 < d)
    (ho : OrthogonalColumns P d) (hfour : 4 ≤ Fintype.card ι)
    (hcong : ∀ j x, d ∣ P x (some j) - P x none) :
    ∃ τ L : α → ℤ, ∃ row : Option ι → α, ∃ s : ℤ,
      (∀ x, τ x = 1 ∨ τ x = -1) ∧ Function.Injective row ∧
      (∀ j x, τ x * P x j = L x - d * unitVector (row j) x) ∧
      0 ≤ s ∧ (∀ j, L (row j) = s) ∧ normSq L = 2 * d * s ∧
      (Fintype.card (Option ι) : ℤ) * s ^ 2 ≤ 2 * d * s ∧
      ∀ j, (∑ x ∈ Finset.univ \ Finset.univ.image row, (τ x * P x j) ^ 2) =
        2 * d * s - (Fintype.card (Option ι) : ℤ) * s ^ 2 := by
  obtain ⟨τ, L, row, hτ, hr, hp⟩ := oriented_class_normal_form P d hd ho hfour hcong
  let P' : α → Option ι → ℤ := fun x j => τ x * P x j
  have hn : ∀ j, normSq (column P' j) = d ^ 2 := by
    intro j
    rw [normSq_eq_dot]
    change dot (fun x => τ x * P x j) (fun x => τ x * P x j) = d ^ 2
    rw [row_signs_preserve_dot τ _ _ hτ]
    have h := ho j j
    change dot (fun x => P x j) (fun x => P x j) = if j = j then d ^ 2 else 0 at h
    simpa using h
  obtain ⟨s, hs0, hs, he⟩ := own_entries_and_energy P' d hd hn L row hp
  refine ⟨τ, L, row, s, hτ, hr, hp, hs0, hs, he, ?_, ?_⟩
  · rw [← he]
    exact own_block_energy_bound L row hr s hs
  · intro j
    exact outside_block_energy P' d s j L row hr hs hp (hn j)

/-- A nonzero residue in any displayed column excludes zero own value. -/
theorem own_value_pos_of_nonzero_residue
    (P : α → β → ℤ) (d s : ℤ) (τ L : α → ℤ) (row : β → α)
    (hτ : ∀ x, τ x = 1 ∨ τ x = -1)
    (hp : ∀ j x, τ x * P x j = L x - d * unitVector (row j) x)
    (hs : 0 ≤ s) (he : normSq L = 2 * d * s)
    (j : β) (hnonzero : ∃ x, ¬d ∣ P x j) : 0 < s := by
  have hne : s ≠ 0 := by
    intro hz
    obtain ⟨x, hx⟩ := hnonzero
    have hsq : L x ^ 2 ≤ normSq L :=
      Finset.single_le_sum (fun k _ => sq_nonneg (L k)) (Finset.mem_univ x)
    have hL : L x = 0 := by rw [he, hz] at hsq; nlinarith [sq_nonneg (L x)]
    have hdiv : d ∣ τ x * P x j := by
      rw [hp, hL]
      exact ⟨-unitVector (row j) x, by ring⟩
    apply hx
    rcases hτ x with h | h <;> simpa [h] using hdiv
  omega

/-- Dividing the block-energy inequality by the positive integer own value
requires no rational division or least-denominator assumption. -/
theorem own_value_linear_bound (k d s : ℤ) (hs : 0 < s)
    (hb : k * s ^ 2 ≤ 2 * d * s) : k * s ≤ 2 * d := by
  nlinarith

end MatrixLargeClass
