module

public import Theory.SpecificGroups.Held.TwoLocalCandidates
public import Theory.SpecificGroups.Held.LocalPairs.Basic
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.Contracts

/-!
# Literal local normalizers for the proper Held extension

The first subgroup is the full automorphism normalizer of the ATLAS max5
subgroup. The second normalizes the actual join of the published pure odd
and two-subgroup candidates. Its definition retains outer automorphisms
which interchange the two max3/max4 classes. Neither subgroup is replaced
by an abstract group of the expected order.

These definitions assert no coverage, order, or core calculation. The
separate coverage and quotient calculations are needed for the intrinsic
proper-extension step in Aschbacher--Smith 15.3.41--42, printed p.1138.
See GLS3 Table 5.3p and the diagnostic scripts in `source/`.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile

/-- The two literal subgroups whose full automorphism normalizers are used.
The second is the pure representative, with indices `(false, 0)`. -/
def innerLocal : Bool → Subgroup Held.He
  | false => Held.TwoLocalCandidates.max5
  | true => Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.candidateProduct false 0

/-- The full normalizer in the actual automorphism group of Held. -/
def candidate (i : Bool) : Subgroup (MulAut Held.He) :=
  Held.LocalPairs.automorphismNormalizer (innerLocal i)

/-- Candidate membership means preservation of the actual subgroup. -/
theorem mem_candidate_iff (i : Bool) (a : MulAut Held.He) :
    a ∈ candidate i ↔ (innerLocal i).map a.toMonoidHom = innerLocal i := Iff.rfl

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile
