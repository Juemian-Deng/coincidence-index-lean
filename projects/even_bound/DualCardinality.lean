import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.Hom.Instances

/-! Exact finite additive dual cardinality. This file does not define or prove
any rational-orthogonal-matrix theorem or coincidence-lattice bound. -/

namespace DualCardinality
/-- The multiplicative tag of the additive cyclic group has all roots needed for duality. -/
theorem enough_roots_zmod (d : ℕ) : HasEnoughRootsOfUnity (Multiplicative (ZMod d)) d where
  prim := ⟨Multiplicative.ofAdd (1 : ZMod d), by
    simpa using IsPrimitiveRoot.orderOf (Multiplicative.ofAdd (1 : ZMod d))⟩
  cyc := by
    apply isCyclic_of_injective
      ((Units.coeHom (Multiplicative (ZMod d))).comp (rootsOfUnity d _).subtype)
    intro a b h
    exact Subtype.ext (Units.ext h)

/-- Exact dual cardinality for every finite abelian group killed by a positive modulus. -/
theorem card_dual (B : Type*) [AddCommGroup B] [Finite B] (d : ℕ) [NeZero d]
    (hkilled : ∀ b : B, d • b = 0) : Nat.card (B →+ ZMod d) = Nat.card B := by
  let := enough_roots_zmod d
  have hdvd : Monoid.exponent (Multiplicative B) ∣ d :=
    Monoid.exponent_dvd_of_forall_pow_eq_one hkilled
  let := HasEnoughRootsOfUnity.of_dvd (Multiplicative (ZMod d)) hdvd
  let e : (B →+ ZMod d) ≃ (Multiplicative B →* (Multiplicative (ZMod d))ˣ) :=
    AddMonoidHom.toMultiplicative.trans (toUnits.monoidHomCongrRightEquiv)
  calc
    Nat.card (B →+ ZMod d) = Nat.card (Multiplicative B →* (Multiplicative (ZMod d))ˣ) := Nat.card_congr e
    _ = Nat.card (Multiplicative B) := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity _ _
    _ = Nat.card B := Nat.card_congr Multiplicative.toAdd

variable {B : Type*} [AddCommGroup B] (d : ℕ)

/-- Vanishing at g is exactly vanishing on its generated additive subgroup. -/
theorem ker_eval_eq (g : B) :
    (AddMonoidHom.eval g : (B →+ ZMod d) →+ ZMod d).ker =
      (AddMonoidHom.domRestrictHom (AddSubgroup.zmultiples g) (ZMod d)).ker := by
  ext f
  change f g = 0 ↔ f.domRestrict (AddSubgroup.zmultiples g) = 0
  rw [AddMonoidHom.domRestrict_eq_zero_iff]
  exact (AddSubgroup.zmultiples_le (g := g) (H := f.ker)).symm

variable [Finite B] [NeZero d]
/-- Evaluation-kernel cardinality equals the cardinality of the quotient by g. -/
theorem card_eval_ker (g : B) (hkilled : ∀ b : B, d • b = 0) :
    Nat.card (AddMonoidHom.eval g : (B →+ ZMod d) →+ ZMod d).ker =
      Nat.card (B ⧸ AddSubgroup.zmultiples g) := by
  rw [ker_eval_eq]
  calc
    _ = Nat.card ((B ⧸ AddSubgroup.zmultiples g) →+ ZMod d) :=
      Nat.card_congr (AddMonoidHom.domRestrictHomKerEquiv (ZMod d) (AddSubgroup.zmultiples g)).toEquiv
    _ = Nat.card (B ⧸ AddSubgroup.zmultiples g) := by
      apply DualCardinality.card_dual _ d
      intro b
      refine QuotientAddGroup.induction_on b ?_
      intro a
      exact (map_nsmul (QuotientAddGroup.mk' (AddSubgroup.zmultiples g)) d a).symm.trans
        (by rw [hkilled]; exact map_zero _)


/-- The quotient-size denominator identity, without natural-number division. -/
theorem card_eval_ker_mul_order (g : B) (hkilled : ∀ b : B, d • b = 0) :
    Nat.card (AddMonoidHom.eval g : (B →+ ZMod d) →+ ZMod d).ker * addOrderOf g =
      Nat.card B := by
  rw [card_eval_ker d g hkilled]
  have h := (AddSubgroup.zmultiples g).index_mul_card
  rwa [AddSubgroup.index_eq_card, Nat.card_zmultiples] at h

/-- The exact evaluation-kernel cardinality used by the written proof. -/
theorem card_eval_ker_eq_div (g : B) (hkilled : ∀ b : B, d • b = 0) :
    Nat.card (AddMonoidHom.eval g : (B →+ ZMod d) →+ ZMod d).ker =
      Nat.card B / addOrderOf g := by
  rw [card_eval_ker d g hkilled, ← AddSubgroup.index_eq_card,
    AddSubgroup.index_eq_card_sub, Nat.card_zmultiples]

/-- Only nonempty fibers are asserted to have this size. No claim that
 evaluation is surjective onto the ambient ZMod d is made. -/
theorem card_nonempty_eval_fiber (g : B) (hkilled : ∀ b : B, d • b = 0)
    (r : ZMod d) (hr : ∃ f : B →+ ZMod d, f g = r) :
    Nat.card {f : B →+ ZMod d // f g = r} = Nat.card B / addOrderOf g := by
  obtain ⟨f, rfl⟩ := hr
  calc
    _ = Nat.card (AddMonoidHom.eval g : (B →+ ZMod d) →+ ZMod d).ker :=
      Nat.card_congr ((AddMonoidHom.eval g : (B →+ ZMod d) →+ ZMod d).fiberEquivKer f)
    _ = _ := card_eval_ker_eq_div d g hkilled

end DualCardinality
