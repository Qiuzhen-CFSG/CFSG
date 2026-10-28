module
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.OriginalTerminal
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.OriginalGeneration

/-!
# The A₆ shadow is excluded once core involutions retain their component

The original marked generation theorem proves rank one of O₂(H); the complete
terminal source assembly then constructs its contradiction. Thus the sole
remaining overcomponent premise is the first claim of source 2.5.26, with the
literal centralizers and component K. No local model or terminal geometry
premise remains.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, 2.5.26 and
completion of Theorem 2.1.1, printed pp.568--570.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The entire A₆ terminal branch from original source data and the genuine
remaining core-involution componenthood conclusion. -/
theorem MathieuSourceSetup.alternating_six_source_false_of_components
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (eK : K ≃* AlternatingSix.ShadowLocal.A6)
    (hc : ∀ i : G, i ∈ twoCore H → orderOf i = 2 →
      IsComponent (centralizer ({i} : Set G)) (K.subgroupOf (centralizer {i}))) : False :=
  MathieuSourceSetup.alternating_six_source_false_of_rank_one c hG hempty hgen hb hstar eK
    (MathieuSourceSetup.alternating_six_source_rank_one_of_components
      c hG hempty hgen hb hstar eK hc)

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
