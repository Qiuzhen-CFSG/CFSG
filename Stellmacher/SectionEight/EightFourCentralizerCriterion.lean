module
public import Stellmacher.SectionEight.EightFourOppositeClosureImage
public import Stellmacher.SectionFiveToSeven.SixFourWitnessCriticalNontrivial
public import Stellmacher.SectionFiveToSeven.VertexLocalModule
public import Stellmacher.SectionThree.LocalFamilyGeneratingExtraction
public import Stellmacher.SectionFiveToSeven.Result6_4

/-!
# The canonical (6.4) criterion at the initial graph edge

In the noncommuting critical-pair context with central first-step center,
let F be the offender fixed subgroup for any faithful quotient-module witness
on the actual initial center. If a vector of F has centralizer in the next
stabilizer generating that stabilizer with the full edge, it belongs to the
next center. No normality of F is assumed.

The central omega-center and (5.1) orient the actual initial and next
stabilizers as P₁ and P₂. The graph center is the canonical Section Six
module. The opposite-center closure identifies F as its centralizer in this
module, so endpoint noncommutation makes F proper. Faithful witness comparison
then gives both canonical critical nontriviality and the full-preimage fixing
condition. The full edge is proper, since otherwise a nontrivial local normal
two-core would contradict the ambient trivial two-core. Unique maximality
therefore promotes generation with that edge to generation with S. Canonical
(6.4) forces the vector into Ω₁(Z(S)), which lies in the next center.

This is the vector-centralizer implication used in Stellmacher (8.4),
journal p.39, and (8.5), p.40, of refs/files/stellmacher-n-group.pdf.
The proof retains the original group, action, and full edge stabilizer.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem normal_of_centralizing
    {G : Type*} [Group G] (W P : Subgroup G) (hle : W ≤ P)
    (hcent : P ≤ Subgroup.centralizer (W : Set G)) : NormalIn W P :=
  ⟨hle, (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
    (hcent.trans (Subgroup.centralizer_le_normalizer _))⟩

private theorem initial_orientation
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    GAt ctx.Γ ctx.criticalPath.a = P1 ∧
      GAt ctx.Γ ctx.criticalPath.firstStep = P2 := by
  let h := ctx.hypothesisTwo.sectionSevenHypotheses ctx.generated
  have hSyl := edge_sylow_data h ctx.Γ ctx.criticalPath
  have homega : omegaOneCenter S ≤ ZAt ctx.Γ ctx.criticalPath.firstStep := by
    obtain ⟨_, U, hU⟩ := hSyl.2
    change omegaOneCenter S ≤ ctx.Γ.zAt _
    rw [ctx.Γ.zAt_def]
    exact le_sSup ⟨U, congrArg omegaOneCenter hU.symm⟩
  have hcentNext : GAt ctx.Γ ctx.criticalPath.firstStep ≤
      Subgroup.centralizer (omegaOneCenter S : Set H) := by
    apply Subgroup.le_centralizer_iff.mpr
    exact homega.trans (hcenter.trans (centerAmbient_le_centralizer _))
  have hnNext : NormalIn (omegaOneCenter S) (GAt ctx.Γ ctx.criticalPath.firstStep) :=
    normal_of_centralizing _ _ ((Subgroup.map_subtype_le _).trans hSyl.2.1) hcentNext
  have hnot : ¬ GAt ctx.Γ ctx.criticalPath.a ≤
      Subgroup.centralizer (omegaOneCenter S : Set H) := by
    intro hcent
    have hn := normal_of_centralizing (omegaOneCenter S) _
      ((Subgroup.map_subtype_le _).trans hSyl.1.1) hcent
    have hza := z_eq_omega_sylow_of_normal ctx.Γ ctx.criticalPath.a hSyl.1 hn
    have hcentral : S ≤ Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H) := by
      rw [show ZAt ctx.Γ ctx.criticalPath.a = omegaOneCenter S from hza]
      exact Subgroup.le_centralizer_iff.mpr
        ((omegaOneCenter_le_centerAmbient S).trans (centerAmbient_le_centralizer S))
    have hcore : S = QAt ctx.Γ ctx.criticalPath.a := by
      change S = q ctx.Γ ctx.criticalPath.a
      rw [← (lemma_seven_four h ctx.Γ ctx.criticalPath).edge_centralizer,
        inf_eq_left.mpr hcentral]
    exact (edge_local_data h ctx.Γ ctx.criticalPath).1.1.1.2.2.2
      (hcore.trans (ctx.Γ.twoCoreAt_def ctx.criticalPath.a))
  have hedge := ctx.criticalPath.edge_stabilizers_are_P
  cases ctx.hypothesisTwo.fiveOne.alternative with
  | a heq hn1 hn2 =>
    rcases hedge with hedge | hedge
    · exact (hn2 (hedge.2 ▸ hnNext)).elim
    · exact (hn1 (hedge.2 ▸ hnNext)).elim
  | c M hmax hne hn1 hn2 _ _ _ _ _ _ _ _ =>
    rcases hedge with hedge | hedge
    · exact (hn2 (hedge.2 ▸ hnNext)).elim
    · exact (hn1 (hedge.2 ▸ hnNext)).elim
  | b heq hstar =>
    rcases hedge with hedge | hedge
    · exact hedge
    · apply (hnot ?_).elim
      simpa only [hedge.1] using hstar.1.1.1

private theorem initial_module
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hGa : GAt ctx.Γ ctx.criticalPath.a = P1) :
    ZAt ctx.Γ ctx.criticalPath.a = sectionSixV S P1 := by
  let h := ctx.hypothesisTwo.sectionSevenHypotheses ctx.generated
  obtain ⟨_, U, hU⟩ := (edge_sylow_data h ctx.Γ ctx.criticalPath).1
  have hlocal := vertexZ_eq_local_vSubgroup ctx.Γ ctx.criticalPath.a U
  have hdata : ∃ U : Sylow 2 P1, (U : Subgroup P1).map P1.subtype = S ∧
      (SectionTwo.vSubgroup U).map P1.subtype = ZAt ctx.Γ ctx.criticalPath.a := by
    apply Eq.mp (congrArg (fun P : Subgroup H =>
      ∃ U : Sylow 2 P, (U : Subgroup P).map P.subtype = S ∧
        (SectionTwo.vSubgroup U).map P.subtype = ZAt ctx.Γ ctx.criticalPath.a) hGa)
    exact ⟨U, hU, hlocal⟩
  obtain ⟨U, hU, hlocal⟩ := hdata
  have hsetup := sectionSix_barred_action_setup ctx.hypothesisTwo
  have hsame : U = sectionSixSylow ctx.hypothesisTwo := by
    apply Sylow.ext
    apply Subgroup.map_injective P1.subtype_injective
    exact hU.trans hsetup.sylow_image.symm
  rw [hsame] at hlocal
  exact hlocal.symm.trans hsetup.localV_image

private theorem fixed_proper
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a)) :
    w.oneJFixedPoints S ≠ ZAt ctx.Γ ctx.criticalPath.a := by
  have himage := le_antisymm (opposite_closure_image_le_oneJ ctx w)
    (eight_four_oneJ_le_of_normal_sylow ctx w (oppositeClosure ctx)
      (opposite_closure_normal_sylow ctx) (opposite_center_le_opposite_closure ctx))
  have hfixed := fixed_center_eq_opposite_closure_centralizer_of_image ctx w himage
  intro heq
  have hcent : ZAt ctx.Γ ctx.criticalPath.a ≤
      Subgroup.centralizer (oppositeClosure ctx : Set H) := by
    rw [heq] at hfixed
    exact hfixed.le.trans inf_le_right
  exact ctx.commutator_ne (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    (hcent.trans (Subgroup.centralizer_le (opposite_center_le_opposite_closure ctx))))

private theorem edge_generation
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (C : Subgroup H)
    (hgenerate : C ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓
      GAt ctx.Γ ctx.criticalPath.firstStep) = GAt ctx.Γ ctx.criticalPath.firstStep) :
    C ⊔ S = GAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let Pa := GAt Γ cp.a
  let P := GAt Γ cp.firstStep
  let D := Pa ⊓ P
  let R := C
  have hlocal := edge_local_data (ctx.hypothesisTwo.sectionSevenHypotheses ctx.generated) Γ cp
  have hPa : Pa ∈ PFamily (⊤ : Subgroup H) S := hlocal.1.1
  have hP : P ∈ SectionThree.PSet (⊤ : Subgroup H) S :=
    (pFamily_iff_pSet _ _ _).mp hlocal.2.1
  have hTD : S ≤ D := cp.S_le_edge_stabilizers
  have hjoin : Pa ⊔ P = ⊤ := by
    change stabilizer Γ cp.a ⊔ stabilizer Γ cp.firstStep = ⊤
    rcases cp.edge_stabilizers_are_P with hedge | hedge
    · rw [hedge.1, hedge.2]
      exact (ctx.hypothesisTwo.sectionSevenHypotheses ctx.generated).generated
    · rw [hedge.1, hedge.2, sup_comm]
      exact (ctx.hypothesisTwo.sectionSevenHypotheses ctx.generated).generated
  have hDproper : D ≠ P := by
    intro he
    have hPPa : P ≤ Pa := he ▸ (inf_le_left : D ≤ Pa)
    have hPatop : Pa = ⊤ := by rwa [sup_eq_left.mpr hPPa] at hjoin
    let Q := QAt Γ cp.a
    have hQne : Q ≠ ⊥ := by
      change q Γ cp.a ≠ ⊥
      rw [q, Γ.twoCoreAt_def]
      exact hPa.1.2.2.1
    have hQp : IsPGroup 2 Q := by
      change IsPGroup 2 (q Γ cp.a)
      rw [q, Γ.twoCoreAt_def]
      exact (pCore_isPGroup (p := 2) (G := Pa)).map Pa.subtype
    have hQn : Q.Normal := by
      apply Subgroup.normalizer_eq_top_iff.mp
      apply top_unique
      rw [← hPatop]
      exact stabilizer_le_normalizer_q Γ cp.a
    have hQle : Q ≤ pCore 2 H := le_sSup ⟨hQn, hQp⟩
    exact hQne (bot_unique (hQle.trans_eq (ctx.hypothesisTwo.sectionSevenHypotheses ctx.generated).twoCore_eq_bot))
  have hRP : R ≤ P := le_sup_left.trans_eq hgenerate
  have hRT : R ⊔ S = P := by
    by_contra hproper
    obtain ⟨M, hM, hTM, huniq⟩ := hP.2
    have hRTM : R ⊔ S ≤ M.map P.subtype :=
      SectionThree.le_unique_maximal_over huniq le_sup_right
        (sup_le hRP (hTD.trans inf_le_right)) hproper
    have hDM : D ≤ M.map P.subtype :=
      SectionThree.le_unique_maximal_over huniq hTD inf_le_right hDproper
    have hPM : P ≤ M.map P.subtype :=
      hgenerate.ge.trans (sup_le (le_sup_left.trans hRTM) hDM)
    apply hM.ne_top
    apply Subgroup.map_injective P.subtype_injective
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact le_antisymm (Subgroup.map_subtype_le _) hPM
  exact hRT

public theorem eight_four_vector_centralizer_criterion
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (v : H) (hv : v ∈ w.oneJFixedPoints S)
    (hgen : (GAt ctx.Γ ctx.criticalPath.firstStep ⊓
      Subgroup.centralizer ({v} : Set H)) ⊔
      (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
        GAt ctx.Γ ctx.criticalPath.firstStep) :
    v ∈ ZAt ctx.Γ ctx.criticalPath.firstStep := by
  obtain ⟨hGa,hNext⟩ := initial_orientation ctx hcenter
  have hV := initial_module ctx hGa
  have homega : omegaOneCenter S ≤ ZAt ctx.Γ ctx.criticalPath.firstStep := by
    obtain ⟨_, U, hU⟩ := (edge_sylow_data
      (ctx.hypothesisTwo.sectionSevenHypotheses ctx.generated) ctx.Γ ctx.criticalPath).2
    change omegaOneCenter S ≤ ctx.Γ.zAt _
    rw [ctx.Γ.zAt_def]
    exact le_sSup ⟨U, congrArg omegaOneCenter hU.symm⟩
  have hcomm : ⁅P2, omegaOneCenter S⁆ = ⊥ := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    rw [Subgroup.le_centralizer_iff]
    exact (homega.trans (hcenter.trans (centerAmbient_le_centralizer _))).trans
      (by rw [hNext])
  have hcyclic : Subgroup.centralizer (Subgroup.zpowers v : Set H) =
      Subgroup.centralizer ({v} : Set H) := by
    ext g
    constructor
    · intro hg
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hg v (Subgroup.mem_zpowers v)).symm
    · intro hg
      rw [Subgroup.mem_centralizer_iff]
      rintro x ⟨n, rfl⟩
      exact (show Commute v g from
        (Subgroup.mem_centralizer_singleton_iff.mp hg).symm).zpow_left n
  have hgenerate : sectionSixCentralizerJoin P2 S v = P2 := by
    unfold sectionSixCentralizerJoin
    rw [hcyclic, ← hNext]
    exact edge_generation ctx _ hgen
  have hcanon : ∀ w' : QuotientModuleWitness P1
      (P1 ⊓ Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a),
      w'.oneJFixedPoints S ≠ ZAt ctx.Γ ctx.criticalPath.a →
      v ∈ w'.oneJFixedPoints S → v ∈ omegaOneCenter S := by
    intro w' hproper hv'
    have hJ := sectionSix_barredCritical_ne_bot_of_witness_fixed_ne
      ctx.hypothesisTwo _ hV w' hproper
    rw [sectionSix_witness_fixed_eq ctx.hypothesisTwo _ hV w'] at hv'
    by_contra hvnot
    exact lemma_six_four S0 S P1 P2 ctx.hypothesisTwo _ hV hcomm hJ
      v hv'.1 hv'.2 hvnot hgenerate.symm
  have htransport := Eq.mpr (congrArg (fun P : Subgroup H =>
    ∀ w' : QuotientModuleWitness P
      (P ⊓ Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a),
      w'.oneJFixedPoints S ≠ ZAt ctx.Γ ctx.criticalPath.a →
      v ∈ w'.oneJFixedPoints S → v ∈ omegaOneCenter S) hGa) hcanon
  exact homega (htransport w (fixed_proper ctx w) hv)

end Stellmacher.SectionEight
