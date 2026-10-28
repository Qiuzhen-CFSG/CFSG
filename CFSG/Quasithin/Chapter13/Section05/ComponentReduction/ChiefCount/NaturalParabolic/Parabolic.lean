module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.NaturalParabolic.Actor
public import Theory.GroupTheory.NoncentralChiefRefinement.ConjugationPullback
public import Theory.Representation.SL2FourNaturalOrbits.BorelCoreCoordinates

/-!
# The one parabolic-core chief interval in 13.5.22

The surjective aligned actor has kernel S intersect L1. Its two-core preimage
is O2(L1). Pulling back the checked noncentral irreducible Borel core action
therefore gives actual one-copy coordinates on this literal relative quotient.
Comparison through L1/(S intersect L1) identifies this actor with the original
five-point stabilizer map. Every chief refinement has count one.

Source: Aschbacher--Smith 13.5.22(2), p.924/PDF p.941, using G.2.4(1).
-/

@[expose] public section
open Subgroup NoncentralChiefRefinement Matrix
open scoped MatrixGroups
noncomputable section
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.NaturalParabolic
open ChapterG.Section02 ChapterG.Section02.Setup
open ChapterG.Section02.AlternatingFive
open ChapterG.Section02.AlternatingFive.Recognition.ProjectiveGeometry
open Representation.SL2FourNatural.BorelFactors Representation.SL2FourNatural.BorelDualCore

variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}
variable (d : Hypothesis D g) (e : D.star D.L ≃* SL(2,F4))
  (he : ((D.star D.L₁).subgroupOf (D.star D.L)).map e.toMonoidHom = B0)

include d in
theorem actor_core_preimage : (pCore 2 B0).comap (actor e he) = (localCore D).val := by
  apply (actor e he).comap_pCore_of_ker_isPGroup (actor_surjective e he)
  rw [actor_kernel d e he]
  exact (isPGroup_pCoreIn 2 (D.I g)).comap_subtype

def actorQuotientEquiv : (D.L₁ ⧸ (core d).val) ≃* B0 :=
  (QuotientGroup.quotientMulEquivOfEq (actor_kernel d e he).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (actor e he) (actor_surjective e he))

/-- The two markings are compared through the same literal residual quotient. -/
def borelMarking : Borel d ≃* B0 :=
  (localQuotientEquiv d).symm.trans (actorQuotientEquiv d e he)

theorem borelMarking_localProjection (k : D.L₁) :
    borelMarking d e he (localProjection d k) = actor e he k := by
  change actorQuotientEquiv d e he ((localQuotientEquiv d).symm (localProjection d k)) = _
  rw [← localQuotientEquiv_mk d k, MulEquiv.symm_apply_apply]
  rfl

def parabolicRepresentation : Representation (ZMod 2) D.L₁ F4 := coreAction.comp (actor e he)

omit [Finite G] in
theorem parabolicRepresentation_irreducible :
    Representation.IsIrreducible (parabolicRepresentation e he) :=
  (Representation.irreducible_comp_surjective_iff _ (actor_surjective e he) _).mpr inferInstance

omit [Finite G] in
theorem parabolicRepresentation_noncentral :
    ∃ k v, parabolicRepresentation e he k v ≠ v := by
  obtain ⟨b,v,hv⟩ := coreAction_noncentral
  obtain ⟨k,rfl⟩ := actor_surjective e he b
  exact ⟨k,v,hv⟩

def parabolicCoordinates :
    SectionCoordinates (core d) (localCore D) (parabolicRepresentation e he) 1 := by
  let R : NormalNode B0 := ⟨pCore 2 B0, show (pCore 2 B0).Normal from inferInstance⟩
  let c := ConjugationPullback.coordinates (actor e he) R coreAction
    borelCoreCoordinates borelCoreCoordinates_equivariant (actor_surjective e he)
  have h0 : ConjugationPullback.kernelNode (actor e he) = core d :=
    Subtype.ext (actor_kernel d e he)
  have h1 : ConjugationPullback.preimageNode (actor e he) R = localCore D :=
    Subtype.ext (actor_core_preimage d e he)
  rw [h0,h1] at c
  exact c

include d e he in
theorem parabolic_chief_of_marking : core d ⋖ localCore D ∧ IsNoncentralTwo (core d) (localCore D) := by
  let := parabolicRepresentation_irreducible e he
  let c := parabolicCoordinates d e he
  have hn := parabolicRepresentation_noncentral e he
  exact ⟨c.covBy (core_le_localCore d) hn, c.isPGroup, c.not_isCentral (by decide) hn⟩

include d e he in
theorem exists_parabolic_refinement_of_marking :
    ∃ t : ChiefSeries D.L₁, t.head = core d ∧ t.last = localCore D ∧
      t.length = 1 ∧ t.noncentralTwoCount = 1 := by
  let := parabolicRepresentation_irreducible e he
  obtain ⟨t,ht0,ht1,htl,htc,_⟩ := (parabolicCoordinates d e he).exists_chief_refinement
    (core_le_localCore d) (parabolicRepresentation_noncentral e he)
  exact ⟨t,ht0,ht1,htl,htc⟩

include d in
/-- The source point-stabilizer always admits a Borel marking; no natural layer is needed here. -/
theorem exists_borel_model : ∃ e : D.star D.L ≃* SL(2,F4),
    ((D.star D.L₁).subgroupOf (D.star D.L)).map e.toMonoidHom = B0 := by
  obtain ⟨e, hu⟩ := d.exists_upper_marked_model d.star_U_sylow
  rw [root_standardPoint] at hu
  refine ⟨e, ?_⟩
  rw [d.star_local_eq_root_normalizer, Subgroup.map_equiv_normalizer_eq, hu]

/-- The original parabolic interval is itself one noncentral two-chief interval. -/
theorem parabolic_chief : core d ⋖ localCore D ∧ IsNoncentralTwo (core d) (localCore D) := by
  obtain ⟨e,he⟩ := exists_borel_model d
  exact parabolic_chief_of_marking d e he

/-- An actual refinement of the literal parabolic-core section. -/
theorem exists_parabolic_refinement :
    ∃ t : ChiefSeries D.L₁, t.head = core d ∧ t.last = localCore D ∧
      t.length = 1 ∧ t.noncentralTwoCount = 1 := by
  obtain ⟨e,he⟩ := exists_borel_model d
  exact exists_parabolic_refinement_of_marking d e he

/-- Jordan--Hölder gives the same count on every refinement of the interval. -/
theorem parabolic_count (t : ChiefSeries D.L₁)
    (ht0 : t.head = core d) (ht1 : t.last = localCore D) :
    t.noncentralTwoCount = 1 := by
  obtain ⟨u,hu0,hu1,_,huc⟩ := exists_parabolic_refinement d
  exact (t.noncentralTwoCount_eq u (ht0.trans hu0.symm) (ht1.trans hu1.symm)).trans huc

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.NaturalParabolic
