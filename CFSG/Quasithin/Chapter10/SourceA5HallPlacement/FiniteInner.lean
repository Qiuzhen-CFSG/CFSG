module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.PairSylow
public import Theory.SpecificGroups.FiniteModelSylowFrattini

/-!
# Inner action on the normal J₃ and McL components

The literal central-quotient equivalence supplies a Sylow Frattini quotient
of order at most128. The original pair's proved Sylow restriction theorem
then forces the original residual into K times its centralizer. This is
an actual inner-action conclusion, preceding any placement of the residual
inside K, and retains the original normalizer and residual maps.

Source: Aschbacher--Smith 4.4.10, printed p.621.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D in
/-- The original residual acts innerly on a normal quasisimple component
whose literal central quotient is the J₃ or McL carrier. -/
theorem source_a5_oddNormalizer_inner_of_j3_or_mcl
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G))) [K.Normal] [IsQuasisimple K]
    (hmodel : Nonempty ((K ⧸ center K) ≃* Sporadic.Janko3.Model) ∨
      Nonempty ((K ⧸ center K) ≃* Sporadic.LeechRelated.McL.Carrier)) :
    ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf (normalizer (B : Set G)) ≤
      K ⊔ centralizer (K : Set (normalizer (B : Set G))) := by
  let P : Sylow 2 (K ⧸ center K) := Classical.choice inferInstance
  apply source_a5_oddNormalizer_inner_of_smallFrattini D e hn hp B hB hBC hperm K P
  rcases hmodel with hj | hm
  · obtain ⟨a⟩ := hj
    exact (Theory.SpecificGroups.FiniteModelSylowFrattini.j3_card_le_thirtytwo a P).trans
      (by decide)
  · obtain ⟨a⟩ := hm
    exact Theory.SpecificGroups.FiniteModelSylowFrattini.mcl_card_le_128 a P

end CFSG.Quasithin.Chapter10
