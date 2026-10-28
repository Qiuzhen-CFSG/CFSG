module
public import Stellmacher.SectionEight.GeneratedEightFiveCentralizerSetup
public import Stellmacher.SectionEight.GeneratedEightFiveActionFromFour
public import Theory.GroupTheory.SpecificGroups.OddDihedralCentralizer

/-!
# Generated initial core quotient from a four-element center

The faithful action kernel is a two-group because its image centralizes
the nontrivial next residual core in the odd-dihedral core quotient.
The ambient centralizer setup supplies (7.7)(a) while keeping Hypothesis Two
on H and the original critical graph on the join.

Source: Stellmacher (8.5), first proof paragraph, printed p.40.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext

open scoped commutatorElement

public theorem generated_eight_five_quotient_of_card_four
    {H : Type*} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4) :
    QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two := by
  classical
  let h := ctx.sectionSeven
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a
  let Z := ZAt Γ cp.a
  let Q := QAt Γ cp.a
  let R := twoCoreIn (EAt Γ cp.firstStep)
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    SevenSix.mem_neighborhood_iff_adjacent Γ |>.mpr cp.firstStep_adj
  have hQP : Q ≤ P := by
    change Γ.twoCoreAt cp.a ≤ _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hZQ : Z ≤ Q :=
    ((lemma_seven_three h Γ).center_core cp.a cp.firstStep hfirst).trans
      (Subgroup.map_subtype_le _)
  have hQnative : Q.subgroupOf P = pCore 2 P := by
    change (Γ.twoCoreAt cp.a).subgroupOf P = _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hRS : R ≤ S.subgroupOf (P1 ⊔ P2) := by
    have hRQ : R ≤ QAt Γ cp.firstStep := by
      change twoCoreIn (Γ.twoResidualAt cp.firstStep) ≤ Γ.twoCoreAt cp.firstStep
      rw [Γ.twoResidualAt_def, Γ.twoCoreAt_def, SevenSix.residual_core_eq_inter_core]
      exact inf_le_right
    exact hRQ.trans (SevenSix.local_cores_le_edge_sylow h Γ cp).2
  have hRP : R ≤ P := hRS.trans (cp.S_le_edge_stabilizers.trans inf_le_left)
  obtain ⟨w⟩ := exists_quotientModuleWitness P Z (hZQ.trans hQP)
    (stabilizer_le_normalizer_z Γ cp.a)
  let := w.groupX
  let := w.finiteX
  obtain ⟨⟨power, ⟨equiv⟩⟩, haction⟩ := eight_five_dihedral_action_of_card_four_local ctx.toLocalContext hcard
  change (P ⧸ pCore 2 P) ≃* DihedralGroup (3 ^ power) at equiv
  let projection : P →* DihedralGroup (3 ^ power) :=
    equiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P))
  have hprojection : projection.ker = pCore 2 P := by
    rw [show projection = equiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P)) from rfl,
      MonoidHom.ker_comp_of_injective _ _ equiv.injective]
    exact QuotientGroup.ker_mk' _
  let actor := (R.subgroupOf P).map projection
  have hactor : IsPGroup 2 actor :=
    ((pCore_isPGroup (G := EAt Γ cp.firstStep) (p := 2)).map
      (EAt Γ cp.firstStep).subtype).comap_subtype.map projection
  have hactorNe : actor ≠ ⊥ := by
    intro hbot
    have hle := (Subgroup.map_eq_bot_iff _).mp hbot
    rw [hprojection, ← hQnative] at hle
    apply (lemma_seven_six h Γ cp).next_residual_core.1
    intro element helement
    exact hle (show (⟨element, hRP helement⟩ : P) ∈ R.subgroupOf P from helement)
  have hcentralizer := DihedralGroup.isPGroup_centralizer_of_nontrivial_two_subgroup
    ((by decide : Odd 3).pow) actor hactor hactorNe
  have hbound := generated_central_first_step_commutator ctx hcenter
  have hkernelImage : w.projection.ker.map projection ≤
      Subgroup.centralizer (actor : Set (DihedralGroup (3 ^ power))) := by
    rintro image ⟨element, helement, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro other ⟨actorElement, hactorElement, rfl⟩
    have helementC : (element : (P1 ⊔ P2 : Subgroup H)) ∈ Subgroup.centralizer (Z : Set (P1 ⊔ P2 : Subgroup H)) := by
      rw [w.kernel_eq] at helement
      exact helement.2
    have hcommQ : ⁅(element : (P1 ⊔ P2 : Subgroup H)), (actorElement : (P1 ⊔ P2 : Subgroup H))⁆ ∈ Q :=
      hbound (Subgroup.commutator_mem_commutator helementC
        ((le_sup_right : R ≤ EAt Γ cp.a ⊔ R) hactorElement))
    have hcomm : ⁅element, actorElement⁆ ∈ projection.ker := by
      rw [hprojection, ← hQnative]
      exact hcommQ
    have hzero : ⁅projection element, projection actorElement⁆ = 1 := by
      rw [← map_commutatorElement]
      exact hcomm
    exact (commutatorElement_eq_one_iff_mul_comm.mp hzero).symm
  have hkernelTwo : IsPGroup 2 w.projection.ker := by
    have hprojTwo : IsPGroup 2 projection.ker := by
      rw [hprojection]
      exact pCore_isPGroup
    exact ((hcentralizer.to_le hkernelImage).comap_of_ker_isPGroup projection
      hprojTwo).to_le (Subgroup.le_comap_map _ _)
  have hkernelCore : w.projection.ker ≤ pCore 2 P :=
    le_sSup ⟨inferInstance, hkernelTwo⟩
  have hcoreKernel : pCore 2 P ≤ w.projection.ker := by
    have hZcentral : Z ≤ Subgroup.centralizer (Q : Set (P1 ⊔ P2 : Subgroup H)) :=
      ((lemma_seven_three h Γ).center_core cp.a cp.firstStep hfirst).trans
        ((SevenSix.omegaOneCenter_le_centerAmbient Q).trans
          (SevenSix.centerAmbient_le_centralizer Q))
    intro element helement
    rw [w.kernel_eq]
    refine ⟨element.property, (Subgroup.le_centralizer_iff.mp hZcentral) ?_⟩
    change element ∈ Q.subgroupOf P
    rwa [hQnative]
  obtain ⟨actionEquiv⟩ := haction w
  refine ⟨actionEquiv.toMonoidHom.comp w.projection,
    actionEquiv.surjective.comp w.surjective, ?_⟩
  rw [MonoidHom.ker_comp_of_injective _ _ actionEquiv.injective,
    le_antisymm hkernelCore hcoreKernel]
  exact hQnative.symm


end Stellmacher.SectionEight
