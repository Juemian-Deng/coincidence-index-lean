import ResidueParityBridge
import DualCardinality
import DualFiberCounting

namespace ActualFiberBounds
open scoped BigOperators

noncomputable section FiniteMaps
noncomputable local instance (α : Type*) : DecidableEq α := Classical.decEq α
variable {ι B : Type*} [AddCommGroup B] [Finite B]
  (d : ℕ) [NeZero d]

omit [Finite B] [NeZero d] in
/-- Every evaluation fiber has at most the actual evaluation-kernel size.
Empty fibers need no surjectivity assumption. -/
theorem eval_fiber_card_le (g : B) (r : ZMod d) :
    Nat.card {f : B →+ ZMod d // f g = r} ≤
      Nat.card (AddMonoidHom.eval g : (B →+ ZMod d) →+ ZMod d).ker := by
  classical
  by_cases hr : ∃ f : B →+ ZMod d, f g = r
  · obtain ⟨f, rfl⟩ := hr
    exact le_of_eq (Nat.card_congr
      ((AddMonoidHom.eval g : (B →+ ZMod d) →+ ZMod d).fiberEquivKer f))
  · have : IsEmpty {f : B →+ ZMod d // f g = r} :=
      ⟨fun f => hr ⟨f.val, f.property⟩⟩
    simp

/-- Actual finite-set counting through one character evaluation fiber. -/
theorem card_le_kernel_mul (S : Finset ι) (F : ι → B →+ ZMod d)
    (g : B) (r : ZMod d) (K : ℕ)
    (hmap : ∀ i ∈ S, F i g = r)
    (hcap : ∀ f, (S.filter (fun i => F i = f)).card ≤ K) :
    S.card ≤ K * Nat.card (AddMonoidHom.eval g : (B →+ ZMod d) →+ ZMod d).ker := by
  classical
  let : Finite (B →+ ZMod d) :=
    Finite.of_injective (fun f : B →+ ZMod d => (f : B → ZMod d)) DFunLike.coe_injective
  let : Fintype (B →+ ZMod d) := Fintype.ofFinite _
  let T : Finset (B →+ ZMod d) := Finset.univ.filter (fun f => f g = r)
  have hc : S.card ≤ K * T.card :=
    Finset.card_le_mul_card_image_of_maps_to
      (by intro i hi; simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]; exact hmap i hi)
      K (by intro f hf; exact hcap f)
  have ht : T.card ≤ Nat.card (AddMonoidHom.eval g : (B →+ ZMod d) →+ ZMod d).ker := by
    simpa [T, Nat.card_eq_fintype_card, Fintype.card_subtype] using eval_fiber_card_le d g r
  exact hc.trans (Nat.mul_le_mul_left K ht)

/-- Zero evaluation gains one missing character, since actual rows are nonzero. -/
theorem card_le_nonzero_kernel_mul (S : Finset ι) (F : ι → B →+ ZMod d)
    (g : B) (K : ℕ)
    (hmap : ∀ i ∈ S, F i g = 0)
    (hnonzero : ∀ i ∈ S, F i ≠ 0)
    (hcap : ∀ f, (S.filter (fun i => F i = f)).card ≤ K) :
    S.card ≤ K * (Nat.card (AddMonoidHom.eval g : (B →+ ZMod d) →+ ZMod d).ker - 1) := by
  classical
  let : Finite (B →+ ZMod d) :=
    Finite.of_injective (fun f : B →+ ZMod d => (f : B → ZMod d)) DFunLike.coe_injective
  let : Fintype (B →+ ZMod d) := Fintype.ofFinite _
  let T : Finset (B →+ ZMod d) := Finset.univ.filter (fun f => f g = 0)
  have hzero : (0 : B →+ ZMod d) ∈ T := by simp [T]
  have hc : S.card ≤ K * (T.erase 0).card :=
    Finset.card_le_mul_card_image_of_maps_to
      (by intro i hi; simp only [Finset.mem_erase, T, Finset.mem_filter, Finset.mem_univ,
          true_and]; exact ⟨hnonzero i hi, hmap i hi⟩)
      K (by intro f hf; exact hcap f)
  have ht : T.card = Nat.card (AddMonoidHom.eval g : (B →+ ZMod d) →+ ZMod d).ker := by
    change T.card = Nat.card {f : B →+ ZMod d // f g = 0}
    simp [T, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simpa only [Finset.card_erase_of_mem hzero, ht] using hc
end FiniteMaps

section Signs
variable {ι A : Type*} [Fintype ι] [AddCommGroup A]
noncomputable local instance (α : Type*) : DecidableEq α := Classical.decEq α

/-- The occupied sign class of an actual row/function, without abstract orbits. -/
noncomputable def signClass (F : ι → A) (i : ι) : Finset ι :=
  Finset.univ.filter (fun k => F k = F i ∨ F k = -F i)

/-- Any orientation of actual rows has individual character fibers bounded
by the original occupied sign classes. -/
theorem oriented_fiber_card_le (F G : ι → A) (S : Finset ι) (K : ℕ)
    (horient : ∀ i, G i = F i ∨ G i = -F i)
    (hcap : ∀ i, (signClass F i).card ≤ K) (f : A) :
    (S.filter (fun i => G i = f)).card ≤ K := by
  classical
  by_cases hn : (S.filter (fun i => G i = f)).Nonempty
  · obtain ⟨k, hk⟩ := hn
    have hkf := (Finset.mem_filter.mp hk).2
    apply (Finset.card_le_card (s := S.filter (fun i => G i = f))
      (t := signClass F k) ?_).trans (hcap k)
    intro i hi
    have hif := (Finset.mem_filter.mp hi).2
    have heq : G i = G k := hif.trans hkf.symm
    simp only [signClass, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases horient i with hi | hi <;> rcases horient k with hk | hk
    · exact Or.inl (hi.symm.trans (heq.trans hk))
    · exact Or.inr (hi.symm.trans (heq.trans hk))
    · exact Or.inr (neg_eq_iff_eq_neg.mp (hi.symm.trans (heq.trans hk)))
    · exact Or.inl (neg_injective (hi.symm.trans (heq.trans hk)))
  · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
    simp
/-- The same occupied-class cap applies to an arbitrary ambient label,
including a label not itself occupied. -/
theorem sign_target_card_le (F : ι → A) (K : ℕ)
    (hcap : ∀ i, (signClass F i).card ≤ K) (a : A) :
    (Finset.univ.filter (fun i => F i = a ∨ F i = -a)).card ≤ K := by
  classical
  by_cases hn : (Finset.univ.filter (fun i => F i = a ∨ F i = -a)).Nonempty
  · obtain ⟨k, hk⟩ := hn
    apply (Finset.card_le_card (t := signClass F k) ?_).trans (hcap k)
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    have hk' := (Finset.mem_filter.mp hk).2
    simp only [signClass, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hi' with hi' | hi' <;> rcases hk' with hk' | hk' <;> simp_all
  · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
    simp
end Signs

section MatrixRows
open ResidueParityBridge
variable {n : ℕ} (P : Matrix (Fin n) (Fin n) ℤ) (d : ℕ)
noncomputable local instance (α : Type*) : DecidableEq α := Classical.decEq α

/-- Orient the actual row functional using its integer selected-column entry. -/
noncomputable def orientedRow (w : Fin n → ℤ) (i : Fin n) : ResidueImage P d →+ ZMod d :=
  if w i < 0 then -rowEvaluation P d i else rowEvaluation P d i

theorem orientedRow_sign (w : Fin n → ℤ) (i : Fin n) :
    orientedRow P d w i = rowEvaluation P d i ∨
      orientedRow P d w i = -rowEvaluation P d i := by
  unfold orientedRow
  split_ifs <;> simp

theorem orientedRow_ne_zero (w : Fin n → ℤ)
    (hrows : ∀ i, rowEvaluation P d i ≠ 0) (i : Fin n) :
    orientedRow P d w i ≠ 0 := by
  unfold orientedRow
  split_ifs <;> simp [hrows]

/-- Exact selected-column evaluation after orientation; no sign quotient or
choice of a scalar representative is used. -/
theorem orientedRow_eval (w : Fin n → ℤ) (j : Fin n) (δ : ℤ)
    (hcol : ∀ i, P i j = δ * w i) (i : Fin n) :
    orientedRow P d w i (columnLabel P d j) = (δ * |w i| : ℤ) := by
  unfold orientedRow
  split_ifs with h
  · rw [AddMonoidHom.neg_apply, rowEvaluation_columnLabel, hcol,
      abs_of_neg h]
    push_cast
    ring
  · rw [rowEvaluation_columnLabel, hcol, abs_of_nonneg (le_of_not_gt h)]

/-- One actual absolute-entry bin has at most K times the evaluation-kernel
size, provided K bounds actual row sign classes. -/
theorem abs_bin_card_le [NeZero d] (w : Fin n → ℤ) (j : Fin n) (δ b : ℤ)
    (K : ℕ) (hcol : ∀ i, P i j = δ * w i)
    (hcap : ∀ i, (signClass (rowEvaluation P d) i).card ≤ K) :
    (Finset.univ.filter (fun i => |w i| = b)).card ≤ K *
      Nat.card (AddMonoidHom.eval (columnLabel P d j) :
        (ResidueImage P d →+ ZMod d) →+ ZMod d).ker := by
  apply card_le_kernel_mul d _ (orientedRow P d w) (columnLabel P d j)
    ((δ*b : ℤ) : ZMod d) K
  · intro i hi
    rw [orientedRow_eval P d w j δ hcol i, (Finset.mem_filter.mp hi).2]
  · exact oriented_fiber_card_le (rowEvaluation P d) (orientedRow P d w) _ K
      (orientedRow_sign P d w) hcap

/-- The actual zero-entry bin omits the zero character. -/
theorem zero_bin_card_le [NeZero d] (w : Fin n → ℤ) (j : Fin n) (δ : ℤ)
    (K : ℕ) (hcol : ∀ i, P i j = δ * w i)
    (hrows : ∀ i, rowEvaluation P d i ≠ 0)
    (hcap : ∀ i, (signClass (rowEvaluation P d) i).card ≤ K) :
    (Finset.univ.filter (fun i => |w i| = 0)).card ≤ K *
      (Nat.card (AddMonoidHom.eval (columnLabel P d j) :
        (ResidueImage P d →+ ZMod d) →+ ZMod d).ker - 1) := by
  apply card_le_nonzero_kernel_mul d _ (orientedRow P d w) (columnLabel P d j) K
  · intro i hi
    rw [orientedRow_eval P d w j δ hcol i, (Finset.mem_filter.mp hi).2]
    simp
  · intro i _
    exact orientedRow_ne_zero P d w hrows i
  · exact oriented_fiber_card_le (rowEvaluation P d) (orientedRow P d w) _ K
      (orientedRow_sign P d w) hcap
end MatrixRows

end ActualFiberBounds
