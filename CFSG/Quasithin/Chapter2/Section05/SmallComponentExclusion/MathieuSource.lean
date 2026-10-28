module
public import CFSG.Quasithin.Chapter2.Section05.SmallComponentExclusion.ResidualOriginalConsumer
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallPersistenceSource
/-!
# Excluding the original Mathieu component

Small-component persistence identifies K with the prime-to-three residual
of C_G(t) for the actual central-core involution. The characteristic local
SL₂(3) residual and the adjusted crossing then contradict the largest-pair
normalizer theorem. Every marking, model action and earlier residual premise
is discharged on the original source tuple.
Source: Aschbacher--Smith, Lemma 2.5.15 (M₁₁ case), printed pp.558--559.
-/
public section
namespace CFSG.Quasithin.Chapter2.Section05
open Subgroup A6Shadow.Frattini ComponentRefinement ComponentSelection ClassificationModels
variable {G : Type*} [Group G] [Finite G] {H K M U L : Subgroup G}
  {S : Sylow 2 H} {z : G}

theorem mathieu_component_false_of_source
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype) (hb : ¬ IsBenderModel K)
    (hp : (U,L) ∈ largestLocalPairs M H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    (e : K ≃* Sporadic.Mathieu.M11) : False := by
  apply mathieu_component_false_of_source_residual c hG hempty hgen hb hp hUS e
  intro t ht htC htZ
  exact (MathieuSourceSetup.small_component_centralizer_residual c hG hempty hgen
    (Or.inr ⟨e⟩) t ht htC htZ).2.2
end CFSG.Quasithin.Chapter2.Section05
