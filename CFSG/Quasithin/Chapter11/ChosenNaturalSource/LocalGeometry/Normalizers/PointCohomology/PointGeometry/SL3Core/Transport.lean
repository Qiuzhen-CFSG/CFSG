module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.SL3Core.Action

/-!
# The original point-local core in the projective action

The proved original L₁/O₂(L₁) ≃ PSL₂ identifies its center as trivial.
Consequently the scalar projective kernel on L₁ lies in O₂(L₁). This gives
an exact core image while allowing the full SL₃ quotient to have odd center.

Source: Aschbacher–Smith 11.1.5, printed pp.765–766. Adapted from the
quotient transport in Closure.Linear.Outside.Multiplicity.RadicalImage.Transport;
the later NaturalPair input is replaced by the original flag quotient.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Matrix
open scoped MatrixGroups commutatorElement
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.SL3Core
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
  (a : SL(3, S.field.Carrier))

def image (A : Subgroup G) : Subgroup (MulAut PSL(3, S.field.Carrier)) :=
  (A.subgroupOf (L ⊔ (T : Subgroup G))).map (projectiveAction D S m a)

theorem image_normalizes (A B : Subgroup G) (hn : B ≤ normalizer (A : Set G)) :
    image D S m a B ≤ normalizer (image D S m a A : Set _) :=
  (map_mono ((comap_mono hn).trans (A.le_normalizer_comap _))).trans (le_normalizer_map _)

theorem core_image_le (A : Subgroup G) (hA : A ≤ L ⊔ (T : Subgroup G)) :
    image D S m a (A.pCoreIn 2) ≤ (image D S m a A).pCoreIn 2 := by
  let B := A.subgroupOf (L ⊔ (T : Subgroup G))
  let f := (projectiveAction D S m a).subgroupMap B
  have hn : ((pCore 2 B).map f).Normal :=
    Normal.map inferInstance f ((projectiveAction D S m a).subgroupMap_surjective B)
  have h : (pCore 2 B).map f ≤ pCore 2 (image D S m a A) :=
    le_sSup ⟨hn,pCore_isPGroup.map f⟩
  have hh := map_mono (f := (image D S m a A).subtype) h
  change ((pCore 2 B).map f).map (B.map (projectiveAction D S m a)).subtype ≤
    (B.map (projectiveAction D S m a)).pCoreIn 2 at hh
  rw [Subgroup.map_map] at hh
  change (pCore 2 B).map ((projectiveAction D S m a).comp B.subtype) ≤ _ at hh
  rw [← Subgroup.map_map] at hh
  change ((A.pCoreIn 2).subgroupOf (L ⊔ (T : Subgroup G))).map _ ≤ _
  rwa [← pCoreIn_subgroupOf 2 A (L ⊔ (T : Subgroup G)) hA]

private theorem coreQuotient_center_eq_bot (flag : InvariantFlag (Coordinates.sl3 m)) :
    center ((flag.Li 0) ⧸ pCore 2 (flag.Li 0)) = ⊥ := by
  apply (center _).eq_bot_iff_forall.mpr
  intro z hz
  apply (SL3.flagLocalCoreEquiv S m flag 0).injective
  rw [map_one]
  apply mem_bot.mp
  rw [← Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot]
  apply mem_center_iff.mpr
  intro b
  obtain ⟨c,rfl⟩ := (SL3.flagLocalCoreEquiv S m flag 0).surjective b
  simpa only [map_mul] using congrArg (SL3.flagLocalCoreEquiv S m flag 0) (mem_center_iff.mp hz c)

/-- The projective kernel on the original L₁ is a two-group, since its
proved PSL₂ quotient is centerless. No centerlessness of the full SL₃ quotient is used. -/
theorem component_kernel_le_core (flag : InvariantFlag (Coordinates.sl3 m))
    (k : (flag.Li 0)) (hk : projectiveAction D S m a (inclusion (((localResidual_le _).trans inf_le_left).trans le_sup_left) k) = 1) :
    k ∈ pCore 2 (flag.Li 0) := by
  apply (QuotientGroup.eq_one_iff k).mp
  apply mem_bot.mp
  rw [← coreQuotient_center_eq_bot D S m flag]
  apply mem_center_iff.mpr
  intro x
  obtain ⟨j,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (flag.Li 0)) x
  have hcomm : ⁅k,j⁆ ∈ pCore 2 (flag.Li 0) := by
    have ha : (⁅k,j⁆ : (flag.Li 0)).val ∈ (flag.Li 0).pCoreIn 2 :=
      inf_pCoreIn_le_of_le 2 ((localResidual_le _).trans inf_le_left)
        ⟨(⁅k,j⁆ : (flag.Li 0)).property,projectiveAction_kernel_commutator D S m a _ hk
          ⟨j,((localResidual_le _).trans inf_le_left) j.property⟩⟩
    obtain ⟨u,hu,he⟩ := ha
    exact (Subtype.ext he : u = ⁅k,j⁆) ▸ hu
  have he := (QuotientGroup.eq_one_iff (N := pCore 2 (flag.Li 0)) ⁅k,j⁆).mpr hcomm
  change QuotientGroup.mk' (pCore 2 (flag.Li 0)) ⁅k,j⁆ = 1 at he
  rw [map_commutatorElement] at he
  exact (commutatorElement_eq_one_iff_mul_comm.mp he).symm

/-- The original O₂(L₁) maps onto the full core of the actual projective L₁ image. -/
theorem closure_image_core (flag : InvariantFlag (Coordinates.sl3 m))
     :
    image D S m a ((flag.Li 0).pCoreIn 2) = (image D S m a (flag.Li 0)).pCoreIn 2 := by
  let M := L ⊔ (T : Subgroup G)
  let B := (flag.Li 0).subgroupOf M
  let f := (projectiveAction D S m a).subgroupMap B
  have hk : f.ker ≤ pCore 2 B := by
    let e : B ≃* (flag.Li 0) := subgroupOfEquivOfLe (((localResidual_le _).trans inf_le_left).trans le_sup_left)
    rw [← pCore_map_iso 2 e.symm]
    intro x hx
    refine ⟨e x,component_kernel_le_core D S m a flag (e x) ?_,?_⟩
    · exact congrArg Subtype.val hx
    · exact e.symm_apply_apply x
  have he := f.comap_pCore_of_ker_isPGroup
    ((projectiveAction D S m a).subgroupMap_surjective B) (pCore_isPGroup.to_le hk)
  have hm : (pCore 2 B).map f = pCore 2 (image D S m a (flag.Li 0)) := by
    rw [← he,map_comap_eq_self_of_surjective ((projectiveAction D S m a).subgroupMap_surjective B)]
    rfl
  have hh := congrArg (Subgroup.map (image D S m a (flag.Li 0)).subtype) hm
  change ((pCore 2 B).map f).map (B.map (projectiveAction D S m a)).subtype =
    (B.map (projectiveAction D S m a)).pCoreIn 2 at hh
  rw [Subgroup.map_map] at hh
  change (pCore 2 B).map ((projectiveAction D S m a).comp B.subtype) = _ at hh
  rw [← Subgroup.map_map] at hh
  change ((((flag.Li 0).pCoreIn 2).subgroupOf M).map (projectiveAction D S m a)) = _
  rw [← pCoreIn_subgroupOf 2 (flag.Li 0) M (((localResidual_le _).trans inf_le_left).trans le_sup_left)]
  exact hh

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.SL3Core
