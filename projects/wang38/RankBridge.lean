import PublishedStatement

namespace Wang38I
open Wang38

/-- The internal one-dimensional residue-space certificate implies literal
Mathlib matrix rank one over the finite field. -/
theorem rankOneMod_rank {p n : ℕ} (hp : OddPrime p) (A : IMatrix n)
    (hA : RankOneMod p A) : (residueMatrix (p := p) A).rank = 1 := by
  classical
  let : Fact (Nat.Prime p) := ⟨oddPrime_isPrime hp⟩
  obtain ⟨⟨i, j, hij⟩, v, _, hv⟩ := hA
  choose c hc using hv
  have he : residueMatrix (p := p) A =
      Matrix.vecMulVec (fun i => (v i : ZMod p)) (fun j => (c j : ZMod p)) := by
    ext i j
    change (A i j : ZMod p) = (v i : ZMod p) * (c j : ZMod p)
    have h := (ZMod.intCast_eq_intCast_iff' _ _ p).mpr (hc j i)
    simpa [mul_comm] using h
  have hle : (residueMatrix (p := p) A).rank ≤ 1 := by
    rw [he]
    exact Matrix.rank_vecMulVec_le _ _
  have hpos : 0 < (residueMatrix (p := p) A).rank := by
    rw [Matrix.rank_eq_finrank_span_cols]
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨(residueMatrix (p := p) A).col j, Submodule.subset_span ⟨j, rfl⟩⟩, ?_⟩
    intro hz
    have h := congrFun (congrArg Subtype.val hz) i
    exact hij ((intCast_mod_zero_iff p _).mp h)
  omega

/-- No prose equivalence is needed in the low-dimensional public assembly. -/
theorem generated_implies_published {p n : ℕ} (hp : OddPrime p)
    (v : IVector n) (Q : QMatrix n) (hQ : GeneratedPrimitive p v Q) :
    PublishedGeneratedPrimitive p v Q := by
  obtain ⟨ho, hr, hl, A, hn, hk, hc⟩ := hQ
  exact ⟨ho, hr, hl, A, hn, rankOneMod_rank hp A hk, hc⟩

#print axioms rankOneMod_rank
#print axioms generated_implies_published
end Wang38I
