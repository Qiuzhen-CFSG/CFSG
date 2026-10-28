module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPushingUpAt
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedNormalSeedPlacement
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedFixedModule
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.AlternatingSixMovedSource

/-!
# The constrained A6 star row cannot contain the original triple-six module

The original normal residual lies in the actual selected component, so
U=[U,Lt] lies in its full moved star group. That group has order at most
32 in the A6 star row, whereas the original U has order64 in its actual
hexacode coordinates. This excludes the row without replacing either
module or imposing a splitting hypothesis.

Source: Aschbacher--Smith C.2.7, B.5.1 and12.7.5, printed pp.146,99--103,840.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The whole original six-space excludes the actual constrained A6 star component. -/
theorem original_tripleSix_point_no_constrained_six_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (J : Subgroup (centralizer ({(t : G)} : Set G))) (hJ : J.IsCComponent)
    (hq : IsQuasisimple (J ⧸ pCore 2 J))
    (hout : ¬ J ≤ (normalizer (K : Set G) ⊓ centralizer ({(t : G)} : Set G)).subgroupOf
      (centralizer ({(t : G)} : Set G)))
    (hf : generalizedFitting J = pCore 2 J)
    (e : starImage (J.map (centralizer ({(t : G)} : Set G)).subtype)
      ((K ⊔ (T : Subgroup G)).pCoreIn 2)
      (J.map (centralizer ({(t : G)} : Set G)).subtype) ≃* alternatingGroup (Fin 6)) : False := by
  let H := centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
  let Jg := J.map H.subtype
  let Q := (K ⊔ (T : Subgroup G)).pCoreIn 2
  let S := Jg ⊔ Q
  have h28 := original_tripleSix_pushingUp_at h structural D a t ht heven
  have hLJ := h28.constrained_normal_seed_le
    (tripleSixPointResidual_component D a t ht heven).1 J hJ hq hout hf
  have hLH : Lt ≤ H := (map_subtype_le _).trans inf_le_right
  have hLJg : Lt ≤ Jg := by
    have hm := map_mono (f := H.subtype) hLJ
    rwa [map_subgroupOf_eq_of_le hLH] at hm
  have hUmoved : U ≤ (⁅starV Jg Q,Jg.subgroupOf S⁆).map S.subtype := by
    rw [map_commutator,map_subgroupOf_eq_of_le (show Jg ≤ S from le_sup_left)]
    conv_lhs => rw [(tripleSixPointCentralizerResidual_commutator D a t ht heven).1]
    exact commutator_mono (h28.constrained_module_le_starV J hJ hq hout hf) hLJg
  have hcardU : Nat.card U = 64 :=
    (Nat.card_congr (tripleSixPointCoordinates D a).toEquiv).trans Atlas.Codes.hexacode_card
  have hbound := ChapterC.C27Source.star_alternatingSix_moved_card_le_thirtyTwo
    (h28.constrained_source_input J hJ hq hout hf) e
  change Nat.card (⁅starV Jg Q,Jg.subgroupOf S⁆ : Subgroup S) ≤ 32 at hbound
  have hle := Nat.card_le_card_of_injective (inclusion hUmoved) (inclusion_injective hUmoved)
  rw [card_map_of_injective S.subtype_injective,hcardU] at hle
  omega

end CFSG.Quasithin.Chapter12.Section07
