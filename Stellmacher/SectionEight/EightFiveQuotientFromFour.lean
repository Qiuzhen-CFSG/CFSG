module

public import Stellmacher.LaterDefs
public import Stellmacher.SectionFiveToSeven.HypothesisTwoToSectionSeven
public import Stellmacher.SectionFiveToSeven.FiveTwoPStarCentralizer
public import Stellmacher.SectionFiveToSeven.Result7_7.CentralizerCommutator
public import Stellmacher.SectionEight.EightFiveDihedralFromFour
public import Theory.GroupTheory.SpecificGroups.OddDihedralCentralizer

/-!
# The actual initial core quotient in Stellmacher (8.5)

In the Section Eight noncommuting critical-pair context, suppose the first-step
center is central in its stabilizer and the initial center has order four.
Then the initial stabilizer modulo its actual two-core is SL₂(2). This
conditional leaf supplies the first conjunct of (8.5) once its parent proves
the four-element-center premise; it neither assumes nor uses (8.5).

The four-center bridge uses (8.1), (7.4), and (3.3) to identify the faithful
center action with SL₂(2) and the ordinary core quotient with an odd dihedral
group. These quotients are kept distinct until the final kernel calculation.
Centrality excludes alternatives (5.1)(a) and (c); alternative (b) makes S an
ambient Sylow and places the next residual subnormally in C_H(Ω₁(Z(S))).
That centralizer's two-core lies in S, supplying the genuine hypotheses of
(7.7)(a). Its bound says that the action kernel centralizes the image of the
next residual's two-core modulo the initial core. This image is nontrivial
by (7.6). The centralizer of a nontrivial two-subgroup in an odd dihedral
group is a two-group, so the normal action kernel is itself a two-group.
It therefore equals the initial two-core, which already centralizes the
initial center by (7.3). The faithful projection now has the required kernel.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.5), first proof
paragraph on journal p.40 / PDF p.30, `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

private theorem omega_le_vertex
    {H : Type*} [Group H] [Finite H] {S P1 P2 : Subgroup H}
    (Γ : CosetGraphContext H S P1 P2) (vertex : Γ.Vertex)
    (hSylow : IsSylowTwoIn S (stabilizer Γ vertex)) :
    omegaOneCenter S ≤ z Γ vertex := by
  obtain ⟨_, sylow, hsylow⟩ := hSylow
  rw [z, Γ.zAt_def]
  exact le_sSup ⟨sylow, congrArg omegaOneCenter hsylow.symm⟩

private theorem normal_omega_of_central_vertex
    {H : Type*} [Group H] [Finite H] {S P1 P2 : Subgroup H}
    (Γ : CosetGraphContext H S P1 P2) (vertex : Γ.Vertex)
    (hSylow : IsSylowTwoIn S (stabilizer Γ vertex))
    (hcenter : z Γ vertex ≤ CenterAmbient (stabilizer Γ vertex)) :
    NormalIn (omegaOneCenter S) (stabilizer Γ vertex) := by
  have hle := (omega_le_vertex Γ vertex hSylow).trans hcenter
  have hsub := hle.trans (Subgroup.map_subtype_le _)
  refine ⟨hsub, (Subgroup.normal_subgroupOf_iff_le_normalizer hsub).mpr ?_⟩
  exact (Subgroup.le_centralizer_iff.mp
    (hle.trans (SevenSix.centerAmbient_le_centralizer _))).trans
      (Subgroup.centralizer_le_normalizer _)

private theorem central_first_step_pstar
    {H : Type*} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    S = (S0 : Subgroup H) ∧
      GAt ctx.Γ ctx.criticalPath.firstStep ∈
        PStarFamily (Subgroup.centralizer (omegaOneCenter S : Set H)) S := by
  have hseven := ctx.hypothesisTwo.sectionSevenHypotheses ctx.generated
  have hsylow := SevenSix.edge_sylow_data hseven ctx.Γ ctx.criticalPath
  have hnormal := normal_omega_of_central_vertex ctx.Γ _ hsylow.2 hcenter
  have hinitial : ¬ stabilizer ctx.Γ ctx.criticalPath.a ≤
      Subgroup.centralizer (omegaOneCenter S : Set H) := by
    intro hcentralInitial
    have hle : omegaOneCenter S ≤ stabilizer ctx.Γ ctx.criticalPath.a :=
      (Subgroup.map_subtype_le _).trans hsylow.1.1
    have hnormalInitial : NormalIn (omegaOneCenter S)
        (stabilizer ctx.Γ ctx.criticalPath.a) :=
      ⟨hle, (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
        (hcentralInitial.trans (Subgroup.centralizer_le_normalizer _))⟩
    have heq := z_eq_omega_sylow_of_normal ctx.Γ _ hsylow.1 hnormalInitial
    apply ctx.commutator_ne
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    rw [heq]
    exact (Subgroup.le_centralizer_iff.mp hcentralInitial).trans
      (Subgroup.centralizer_le
        (lemma_seven_four hseven ctx.Γ ctx.criticalPath).reverse_containment.1)
  cases ctx.hypothesisTwo.fiveOne.alternative with
  | a hS hleft hright =>
      rcases ctx.criticalPath.edge_stabilizers_are_P with hedge | hedge
      · exact (hright (hedge.2 ▸ hnormal)).elim
      · exact (hleft (hedge.2 ▸ hnormal)).elim
  | b hS hpstar =>
      refine ⟨hS, ?_⟩
      rcases ctx.criticalPath.edge_stabilizers_are_P with hedge | hedge
      · change stabilizer ctx.Γ ctx.criticalPath.firstStep ∈ _
        rwa [hedge.2]
      · exfalso
        apply hinitial
        rw [hedge.1]
        exact hpstar.1.1.1
  | c maximal hmax hS hleft hright hJleft hJright hPleft hPright hNleft hNright hstable htransfer =>
      rcases ctx.criticalPath.edge_stabilizers_are_P with hedge | hedge
      · exact (hright (hedge.2 ▸ hnormal)).elim
      · exact (hleft (hedge.2 ▸ hnormal)).elim

private theorem central_first_step_commutator
    {H : Type*} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    ⁅Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H),
      EAt ctx.Γ ctx.criticalPath.a ⊔
        twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)⁆ ≤
      QAt ctx.Γ ctx.criticalPath.a := by
  obtain ⟨hS, hpstar⟩ := central_first_step_pstar ctx hcenter
  let centralizer := Subgroup.centralizer (omegaOneCenter S : Set H)
  have hsubnormal : SubnormalIn (e ctx.Γ ctx.criticalPath.firstStep) centralizer := by
    change SubnormalIn (ctx.Γ.twoResidualAt _) _
    rw [ctx.Γ.twoResidualAt_def]
    have hresult := pstar_residual_subnormal_in_omegaCentralizer S0
      (GAt ctx.Γ ctx.criticalPath.firstStep) (by simpa [hS] using hpstar)
    simpa only [centralizer, hS, GAt, stabilizer] using hresult
  have hSC : S ≤ centralizer := by
    exact Subgroup.le_centralizer_iff.mp
      ((SevenSix.omegaOneCenter_le_centerAmbient S).trans
        (SevenSix.centerAmbient_le_centralizer S))
  have hcore : twoCoreIn centralizer ≤ S := by
    have hS0C : (S0 : Subgroup H) ≤ centralizer := hS ▸ hSC
    let sylow := S0.subtype hS0C
    have hbound := Subgroup.map_mono (f := centralizer.subtype)
      ((pCore_isPGroup (G := centralizer) (p := 2)).le_sylow_of_normal sylow)
    change (pCore 2 centralizer).map centralizer.subtype ≤
      ((S0.subtype hS0C : Sylow 2 centralizer) : Subgroup centralizer).map
        centralizer.subtype at hbound
    rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hS0C, ← hS] at hbound
    exact hbound
  exact lemma_seven_seven_centralizer_commutator
    (ctx.hypothesisTwo.sectionSevenHypotheses ctx.generated)
    ctx.Γ ctx.criticalPath centralizer rfl hsubnormal hcore


open scoped commutatorElement

public theorem eight_five_quotient_of_card_four
    {H : Type*} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4) :
    QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two := by
  classical
  let h := ctx.hypothesisTwo.sectionSevenHypotheses ctx.generated
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
  have hRS : R ≤ S := by
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
  obtain ⟨⟨power, ⟨equiv⟩⟩, haction⟩ := eight_five_dihedral_action_of_card_four ctx hcard
  let projection : P →* DihedralGroup (3 ^ power) :=
    equiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P))
  have hprojection : projection.ker = pCore 2 P := by
    rw [MonoidHom.ker_comp_of_injective _ _ equiv.injective]
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
  have hbound := central_first_step_commutator ctx hcenter
  have hkernelImage : w.projection.ker.map projection ≤
      Subgroup.centralizer (actor : Set (DihedralGroup (3 ^ power))) := by
    rintro image ⟨element, helement, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro other ⟨actorElement, hactorElement, rfl⟩
    have helementC : (element : H) ∈ Subgroup.centralizer (Z : Set H) := by
      rw [w.kernel_eq] at helement
      exact helement.2
    have hcommQ : ⁅(element : H), (actorElement : H)⁆ ∈ Q :=
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
    have hZcentral : Z ≤ Subgroup.centralizer (Q : Set H) :=
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
