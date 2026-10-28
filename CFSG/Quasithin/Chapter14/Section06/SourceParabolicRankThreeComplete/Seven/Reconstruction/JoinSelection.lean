module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.Reconstruction.MovedAction
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.MSRestriction
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ExceptionalSevenControl.Restriction

/-!
# Block reconstruction when the residual-radical product fills the ambient group

The C.2.7 star module is defined on KR. When this is the original ambient
group, the full B.5 action and the original Sylow normalizer obstruction
feed C.1.24 directly. The proof constructs shortness and then types the
whole block; equivalence transport returns the original component.

The residual-join equality is kept explicit here. Its proof must extend
the full natural or exceptional moved action to the original ambient group.
Source: Aschbacher--Smith, C.2.7 and14.6.10(5), pp.145--147 and1029.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.Seven.Reconstruction
open ChapterC Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly
variable {G : Type*} [Group G] [Finite G]

/-- The remaining group-theoretic bridge. The explicit full star action is
already constructed from B.5; this contract contains no block conclusion. -/
def ResidualJoinInput : Prop :=
  ∀ (H K R M : Subgroup G) (_h : Input KnownSimple.IsKnownSimple H R M K),
    K = (pResidual 2 H).map H.subtype →
    MSOddIndexRadical (R.subgroupOf H) →
    (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7) →
    AlternatingModels.ActionData (starRepresentation K R) (starImage K R K) →
    H = K ⊔ R

private theorem perfect_twoPerfect {A : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] : IsPPerfect 2 A := by
  intro N hn hp
  let := hn
  let : Group.IsNilpotent (A ⧸ N) := hp.isNilpotent
  apply top_unique
  rw [←solvableResidual_eq_top (G := A)]
  exact solvableResidual_le_of_solvable_quotient N

/-- The full star action reconstructs the original block once the ambient
join and its actual Baumann obstruction are supplied. -/
theorem block_types_of_join_eq {H K R M : Subgroup G}
    (h : Input KnownSimple.IsKnownSimple H R M K) (hjoin : H = K ⊔ R)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (P : Sylow 2 H)
    (hprod : ∀ g : H, ∃ k ∈ K.subgroupOf H, ∃ t ∈ (P : Subgroup H), k*t=g)
    (hno : ∀ D : Subgroup (ChapterB.baumann (P : Subgroup H)),
      D.Characteristic → D ≠ ⊥ → ¬ (D.map (ChapterB.baumann (P : Subgroup H)).subtype).Normal) :
    IsAlternatingBlock K 7 ∨ IsExceptionalA7Block K := by
  subst H
  let B := K.subgroupOf (K ⊔ R)
  let V := starV K R
  let q := QuotientGroup.mk' (starKernel K R)
  let : B.Normal := normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
  let a : B ≃* K := subgroupOfEquivOfLe (show K ≤ K ⊔ R from le_sup_left)
  let : IsQuasisimple (K ⧸ pCore 2 K) := h.quasisimple
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm
  let : Group.IsPerfect B := h.component.2.perfect
  let : IsElementaryAbelian 2 (⁅V,B⁆ : Subgroup (K ⊔ R : Subgroup G)) :=
    IsElementaryAbelian.of_le (commutator_le_left V B)
  have hfB : generalizedFitting B = pCore 2 B := by
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [map_generalizedFitting_equiv,pCore_map_iso,h.fitting]
  obtain ⟨m⟩ := star_actionData h e
  have hdata := moved_wholeModule V B q (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) m ((sevenStarEquiv h e).symm.trans e)
  have hm : ⁅⁅V,B⁆,B⁆ = ⁅V,B⁆ := commutator_isPPerfect_idempotent B V perfect_twoPerfect
    (IsElementaryAbelian.isPGroup 2 V) le_normalizer_of_normal
  have hb := block_types_of_wholeModule B ⁅V,B⁆ h.component.2
    (C27Source.source_join_fitting h) hfB P hprod hno hm hdata.1 hdata.2
  exact hb.imp (RankOne.Solvable.isAlternatingBlock_of_equiv a) (RankOne.ExceptionalSevenControl.exceptional_of_equiv a)

end CFSG.Quasithin.Chapter14.Section06.Seven.Reconstruction
