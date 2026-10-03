module
public import Stellmacher.LaterDefs
public import Stellmacher.SectionFiveToSeven.HypothesisTwoToSectionSeven
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Stellmacher.SectionFiveToSeven.FiveTwoPStarCentralizer
public import Theory.GroupTheory.PGroup.SubnormalCore

/-!
# Ambient centralizer core control in Stellmacher (8.5)

Assume the first-step center is central in its stabilizer and the endpoint
commutator equals both the first-step and penultimate centers. The two-core
of the first-step residual lies in the ambient commutator centralizer's
two-core, which in turn lies in the penultimate vertex core. The public
statement retains the four-element initial center, SL₂(2) core quotient,
and long-path hypotheses of the consuming distance argument.

Centrality makes the Sylow omega-center normal at the first step. The
initial critical-edge centralizer equality excludes normality at the
initial vertex. These facts exclude alternatives (a) and (c) of Hypothesis
Two and orient alternative (b): the edge Sylow is genuinely global and the
first-step group is the given P-star member. Its residual is therefore
subnormal in the full omega-center centralizer, so subnormal core
monotonicity gives the first inclusion.

For the other inclusion, every vertex stabilizer contains a global Sylow
by conjugacy. It normalizes its vertex center, hence that center's
centralizer and its characteristic two-core. A two-subgroup normalized by
a global Sylow lies in that Sylow. Thus the centralizer core lies in the
vertex stabilizer and is normal there, proving containment in its core.
This argument needs no hereditary Hypothesis Two, no assertion that a
centralizer is two-local, and none of (7.7)'s extra explicit hypotheses.

Source: B. Stellmacher, Journal of Algebra 190 (1997), proof of (8.5),
journal pp.40–41 / PDF pp.30–31, `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionEight
open Stellmacher.Later Stellmacher.SectionsFiveToSeven
open CosetGraphContext

private theorem omega_le_z
    {H : Type*} [Group H] [Finite H]
    {S P1 P2 : Subgroup H} (Γ : CosetGraphContext H S P1 P2)
    (d : Γ.Vertex) (hS : IsSylowTwoIn S (GAt Γ d)) :
    omegaOneCenter S ≤ ZAt Γ d := by
  obtain ⟨_, T, hT⟩ := hS
  rw [ZAt, z, Γ.zAt_def]
  exact le_sSup ⟨T, congrArg omegaOneCenter hT.symm⟩

private theorem normal_of_le_center
    {H : Type*} [Group H] (A P : Subgroup H)
    (hA : A ≤ CenterAmbient P) : NormalIn A P := by
  have hAP : A ≤ P := hA.trans (Subgroup.map_subtype_le _)
  refine ⟨hAP, (Subgroup.normal_subgroupOf_iff_le_normalizer hAP).mpr ?_⟩
  apply (Subgroup.centralizer_le_normalizer (A : Set H)).trans'
  apply Subgroup.le_centralizer_iff.mpr
  exact hA.trans (SevenSix.centerAmbient_le_centralizer P)

private theorem central_setup
    {H : Type*} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    S = (S0 : Subgroup H) ∧
      ZAt ctx.Γ ctx.criticalPath.firstStep = omegaOneCenter S ∧
      SubnormalIn (EAt ctx.Γ ctx.criticalPath.firstStep)
        (Subgroup.centralizer (omegaOneCenter S : Set H)) := by
  let h := ctx.hypothesisTwo.sectionSevenHypotheses ctx.generated
  have hSyl := SevenSix.edge_sylow_data h ctx.Γ ctx.criticalPath
  have hnormal : NormalIn (omegaOneCenter S)
      (GAt ctx.Γ ctx.criticalPath.firstStep) :=
    normal_of_le_center _ _ ((omega_le_z _ _ hSyl.2).trans hcenter)
  have hz := z_eq_omega_sylow_of_normal ctx.Γ ctx.criticalPath.firstStep hSyl.2 hnormal
  have hnot : ¬ NormalIn (omegaOneCenter S)
      (GAt ctx.Γ ctx.criticalPath.a) := by
    intro hn
    have hza := z_eq_omega_sylow_of_normal ctx.Γ ctx.criticalPath.a hSyl.1 hn
    have hcentral : S ≤ Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H) := by
      rw [show ZAt ctx.Γ ctx.criticalPath.a = omegaOneCenter S from hza]
      exact Subgroup.le_centralizer_iff.mpr
        ((SevenSix.omegaOneCenter_le_centerAmbient S).trans
          (SevenSix.centerAmbient_le_centralizer S))
    have hcore : S = QAt ctx.Γ ctx.criticalPath.a := by
      change S = q ctx.Γ ctx.criticalPath.a
      rw [← (lemma_seven_four h ctx.Γ ctx.criticalPath).edge_centralizer,
        inf_eq_left.mpr hcentral]
    exact (SevenSix.edge_local_data h ctx.Γ ctx.criticalPath).1.1.1.2.2.2
      (hcore.trans (ctx.Γ.twoCoreAt_def ctx.criticalPath.a))
  have hbranches : S = (S0 : Subgroup H) ∧
      GAt ctx.Γ ctx.criticalPath.firstStep = P2 := by
    cases ctx.hypothesisTwo.fiveOne.alternative with
    | a heq hn1 hn2 =>
      rcases ctx.criticalPath.edge_stabilizers_are_P with hedge | hedge
      · exact (hn2 (hedge.2 ▸ hnormal)).elim
      · exact (hn1 (hedge.2 ▸ hnormal)).elim
    | b heq hstar =>
      refine ⟨heq, ?_⟩
      rcases ctx.criticalPath.edge_stabilizers_are_P with hedge | hedge
      · exact hedge.2
      · exfalso
        apply hnot
        change NormalIn (omegaOneCenter S) (stabilizer ctx.Γ ctx.criticalPath.a)
        rw [hedge.1]
        apply normal_of_le_center
        have hle : omegaOneCenter S ≤ P2 :=
          (SevenSix.omegaOneCenter_le_centerAmbient S).trans
            ((Subgroup.map_subtype_le _).trans h.P2_mem.1.2.1.1)
        intro x hx
        refine ⟨⟨x, hle hx⟩, ?_, rfl⟩
        apply Subgroup.mem_center_iff.mpr
        intro y
        apply Subtype.ext
        exact (Subgroup.mem_centralizer_iff.mp (hstar.1.1.1 y.2) x hx).symm
    | c M hmax hne hn1 hn2 _ _ _ _ _ _ _ _ =>
      rcases ctx.criticalPath.edge_stabilizers_are_P with hedge | hedge
      · exact (hn2 (hedge.2 ▸ hnormal)).elim
      · exact (hn1 (hedge.2 ▸ hnormal)).elim
  refine ⟨hbranches.1, hz, ?_⟩
  cases ctx.hypothesisTwo.fiveOne.alternative with
  | a heq hn1 hn2 => exact (hn2 (hbranches.2 ▸ hnormal)).elim
  | b heq hstar =>
    rw [show EAt ctx.Γ ctx.criticalPath.firstStep =
      twoResidualIn (GAt ctx.Γ ctx.criticalPath.firstStep) from
        ctx.Γ.twoResidualAt_def ctx.criticalPath.firstStep, hbranches.2]
    subst S
    exact pstar_residual_subnormal_in_omegaCentralizer S0 P2 hstar
  | c M hmax hne hn1 hn2 _ _ _ _ _ _ _ _ => exact (hne hbranches.1).elim

private theorem vertex_centralizer_core
    {H : Type*} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hglobal : S = (S0 : Subgroup H)) (d : ctx.Γ.Vertex) :
    twoCoreIn (Subgroup.centralizer (ZAt ctx.Γ d : Set H)) ≤ QAt ctx.Γ d := by
  let h := ctx.hypothesisTwo.sectionSevenHypotheses ctx.generated
  let C := Subgroup.centralizer (ZAt ctx.Γ d : Set H)
  let Q := twoCoreIn C
  have hNcore : Subgroup.normalizer (C : Set H) ≤ Subgroup.normalizer (Q : Set H) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro g hg x hx
    obtain ⟨xc, hxc, rfl⟩ := hx
    let actor : Subgroup.normalizer (C : Set H) := ⟨g, hg⟩
    let aut := Subgroup.normalizerMonoidHom C actor
    have hfix : (pCore 2 C).comap aut.toMonoidHom = pCore 2 C :=
      (inferInstance : (pCore 2 C).Characteristic).fixed aut
    have himage : aut xc ∈ pCore 2 C := by
      change xc ∈ (pCore 2 C).comap aut.toMonoidHom
      rwa [hfix]
    exact ⟨aut xc, himage, by
      simp [aut, actor, mul_assoc, Subgroup.normalizerMonoidHom_apply_apply_coe]⟩
  have hNC : Subgroup.normalizer (ZAt ctx.Γ d : Set H) ≤
      Subgroup.normalizer (C : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer (ZAt ctx.Γ d : Set H))).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer _)
  have hGQ : GAt ctx.Γ d ≤ Subgroup.normalizer (Q : Set H) :=
    (stabilizer_le_normalizer_z ctx.Γ d).trans (hNC.trans hNcore)
  have hSyl : ∃ T : Sylow 2 H, (T : Subgroup H) ≤ GAt ctx.Γ d := by
    obtain ⟨g, hg⟩ := (lemma_seven_one h ctx.Γ).vertex_stabilizers_conjugate d
    let T := S0.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective
    refine ⟨T, ?_⟩
    change (S0 : Subgroup H).map (MulAut.conj g).toMonoidHom ≤ stabilizer ctx.Γ d
    rw [← hglobal]
    rcases hg with hg | hg
    · rw [hg]
      exact Subgroup.map_mono h.P1_mem.1.2.1.1
    · rw [hg]
      exact Subgroup.map_mono h.P2_mem.1.2.1.1
  obtain ⟨T, hTG⟩ := hSyl
  have hQp : IsPGroup 2 Q := (pCore_isPGroup (G := C) (p := 2)).map C.subtype
  have hQT : Q ≤ (T : Subgroup H) := by
    have heq := T.is_maximal'
      (T.isPGroup'.to_sup_of_normal_right' hQp (hTG.trans hGQ)) le_sup_left
    exact le_sup_right.trans heq.le
  have hQG : Q ≤ GAt ctx.Γ d := hQT.trans hTG
  have hnormal : (Q.subgroupOf (GAt ctx.Γ d)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQG).mpr hGQ
  have hQpG : IsPGroup 2 (Q.subgroupOf (GAt ctx.Γ d)) :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQG).symm
  have hcore : Q.subgroupOf (GAt ctx.Γ d) ≤ pCore 2 (GAt ctx.Γ d) :=
    le_sSup ⟨hnormal, hQpG⟩
  have hmap := Subgroup.map_mono (f := (GAt ctx.Γ d).subtype) hcore
  rw [Subgroup.map_subgroupOf_eq_of_le hQG] at hmap
  exact hmap.trans_eq (ctx.Γ.twoCoreAt_def d).symm

/-- The two ambient core containments in the long-path argument of (8.5). -/
public theorem eight_five_centralizer_core_control
    {H : Type*} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (_hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (_hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlen : 2 < ctx.criticalPath.length)
    (hfirst : ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ ctx.criticalPath.a'⁆ =
      ZAt ctx.Γ ctx.criticalPath.firstStep)
    (hlast : ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ ctx.criticalPath.a'⁆ =
      ZAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, by omega⟩)) :
    let R := ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ ctx.criticalPath.a'⁆
    let C := Subgroup.centralizer (R : Set H)
    twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep) ≤ twoCoreIn C ∧
      twoCoreIn C ≤
        QAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, by omega⟩) := by
  obtain ⟨hglobal, hz, hsub⟩ := central_setup ctx hcenter
  dsimp only
  constructor
  · rw [hfirst, hz]
    exact pCoreAmbient_mono_of_isSubnormalIn _ _ 2 hsub.1 hsub.2
  · rw [hlast]
    exact vertex_centralizer_core ctx hglobal _

end Stellmacher.SectionEight
