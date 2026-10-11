import RationalNeighborRealization
import PrimeThree
import UnitSplitting
import UnimodularGram

/-! Complete literal published Wang–Wang–Yu Conjecture 38, both parts.
The low-rank lattice classification is proved in the imported sources.
No classification theorem is supplied as an assumption or custom axiom. -/
namespace Wang38

theorem published_conjecture38I : PublishedConjecture38I :=
  Wang38I.published_conjecture38I

theorem published_conjecture38 : PublishedConjecture38I ∧ PublishedConjecture38II :=
  ⟨published_conjecture38I, published_conjecture38II⟩

#print PublishedConjecture38I
#print PublishedConjecture38II
#print PublishedGeneratedPrimitive
#print ExactLevel
#print Admissible
#print FullSupport
#print axioms published_conjecture38I
#print axioms published_conjecture38II
#print axioms published_conjecture38
end Wang38
