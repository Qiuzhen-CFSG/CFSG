module
public import Stellmacher.SectionEight.GeneratedContext
public import Stellmacher.SectionFiveToSeven.Result7_7.CentralizerCommutator
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Stellmacher.SectionFiveToSeven.FiveTwoPStarCentralizer
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift

/-!
# Ambient centralizer setup for generated Stellmacher (8.5)

Centrality of the first-step center orients ambient Hypothesis Two's
alternative (b). Thus S is the ambient Sylow and the mapped first-step
residual is subnormal in the ambient Sylow omega-center centralizer.
Subnormality pulls back along the join inclusion. The restricted centralizer
has two-core contained in the restricted Sylow, giving the genuine inputs
of (7.7)(a) on the original generated critical graph.

The setup and center equality also supply the generated distance argument.
Hypothesis Two is never imposed on the join. Source: Stellmacher (8.5),
printed pp.40–41, and the P-star reduction (5.2).
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

private theorem normal_of_centralizing
    {G : Type*} [Group G] (W P : Subgroup G) (hle : W ≤ P)
    (hcent : P ≤ Subgroup.centralizer (W : Set G)) : NormalIn W P := by
  exact ⟨hle, (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
    (hcent.trans (Subgroup.centralizer_le_normalizer (W : Set G)))⟩

public theorem generated_central_first_step_setup
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    S = (S0 : Subgroup H) ∧
    (GAt ctx.Γ ctx.criticalPath.a).map (P1 ⊔ P2).subtype = P1 ∧
    (GAt ctx.Γ ctx.criticalPath.firstStep).map (P1 ⊔ P2).subtype = P2 ∧
    SubnormalIn ((EAt ctx.Γ ctx.criticalPath.firstStep).map (P1 ⊔ P2).subtype)
      (Subgroup.centralizer (omegaOneCenter S : Set H)) := by
  let G := (P1 ⊔ P2 : Subgroup H)
  let embedding : G →* H := (P1 ⊔ P2).subtype
  let T := S.subgroupOf (P1 ⊔ P2)
  have hinjective : Function.Injective embedding := (P1 ⊔ P2).subtype_injective
  have hmapS : T.map embedding = S := Subgroup.map_subgroupOf_eq_of_le
    (ctx.hypothesisTwo.fiveOne.P1_mem.1.2.1.1.trans le_sup_left)
  have hmapA : (P1.subgroupOf (P1 ⊔ P2)).map embedding = P1 :=
    Subgroup.map_subgroupOf_eq_of_le le_sup_left
  have hmapB : (P2.subgroupOf (P1 ⊔ P2)).map embedding = P2 :=
    Subgroup.map_subgroupOf_eq_of_le le_sup_right
  have hSyl := SevenSix.edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath
  have homega : (omegaOneCenter T).map embedding = omegaOneCenter S := by
    rw [← hmapS]
    exact (omegaOneCenterAmbient_map_injective embedding hinjective T).symm
  have homegaNext : omegaOneCenter T ≤ ZAt ctx.Γ ctx.criticalPath.firstStep := by
    obtain ⟨_, sylow, hsylow⟩ := hSyl.2
    rw [ZAt, z, ctx.Γ.zAt_def]
    exact le_sSup ⟨sylow, congrArg omegaOneCenter hsylow.symm⟩
  have hcentNext : GAt ctx.Γ ctx.criticalPath.firstStep ≤
      Subgroup.centralizer (omegaOneCenter T : Set G) :=
    Subgroup.le_centralizer_iff.mpr
      ((homegaNext.trans hcenter).trans (SevenSix.centerAmbient_le_centralizer _))
  have hnormal : NormalIn (omegaOneCenter S)
      ((GAt ctx.Γ ctx.criticalPath.firstStep).map embedding) := by
    apply normal_of_centralizing
    · rw [← homega]
      exact Subgroup.map_mono ((Subgroup.map_subtype_le _).trans hSyl.2.1)
    · rintro element ⟨preimage, hpreimage, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro member hmember
      rw [← homega] at hmember
      obtain ⟨old, hold, rfl⟩ := hmember
      simpa using congrArg embedding
        (Subgroup.mem_centralizer_iff.mp (hcentNext hpreimage) old hold)
  have hnot : ¬ GAt ctx.Γ ctx.criticalPath.a ≤
      Subgroup.centralizer (omegaOneCenter T : Set G) := by
    intro hcent
    have hn := normal_of_centralizing (omegaOneCenter T) _
      ((Subgroup.map_subtype_le _).trans hSyl.1.1) hcent
    have hza := z_eq_omega_sylow_of_normal ctx.Γ ctx.criticalPath.a hSyl.1 hn
    have hcentral : T ≤ Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G) := by
      rw [show ZAt ctx.Γ ctx.criticalPath.a = omegaOneCenter T from hza]
      exact Subgroup.le_centralizer_iff.mpr
        ((SevenSix.omegaOneCenter_le_centerAmbient T).trans
          (SevenSix.centerAmbient_le_centralizer T))
    have hcore : T = QAt ctx.Γ ctx.criticalPath.a := by
      change T = q ctx.Γ ctx.criticalPath.a
      rw [← (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).edge_centralizer,
        inf_eq_left.mpr hcentral]
    exact (SevenSix.edge_local_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1.1.1.2.2.2
      (hcore.trans (ctx.Γ.twoCoreAt_def ctx.criticalPath.a))
  have hedge :
      ((GAt ctx.Γ ctx.criticalPath.a).map embedding = P1 ∧
        (GAt ctx.Γ ctx.criticalPath.firstStep).map embedding = P2) ∨
      ((GAt ctx.Γ ctx.criticalPath.a).map embedding = P2 ∧
        (GAt ctx.Γ ctx.criticalPath.firstStep).map embedding = P1) := by
    rcases ctx.criticalPath.edge_stabilizers_are_P with hedge | hedge
    · exact Or.inl ⟨(congrArg (Subgroup.map embedding) hedge.1).trans hmapA,
        (congrArg (Subgroup.map embedding) hedge.2).trans hmapB⟩
    · exact Or.inr ⟨(congrArg (Subgroup.map embedding) hedge.1).trans hmapB,
        (congrArg (Subgroup.map embedding) hedge.2).trans hmapA⟩
  cases ctx.hypothesisTwo.fiveOne.alternative with
  | a heq hn1 hn2 =>
    rcases hedge with hedge | hedge
    · exact (hn2 (hedge.2 ▸ hnormal)).elim
    · exact (hn1 (hedge.2 ▸ hnormal)).elim
  | c M hmax hne hn1 hn2 _ _ _ _ _ _ _ _ =>
    rcases hedge with hedge | hedge
    · exact (hn2 (hedge.2 ▸ hnormal)).elim
    · exact (hn1 (hedge.2 ▸ hnormal)).elim
  | b heq hstar =>
    have hnextmap : (GAt ctx.Γ ctx.criticalPath.firstStep).map embedding = P2 := by
      rcases hedge with hedge | hedge
      · exact hedge.2
      · exfalso
        apply hnot
        intro element helement
        have himage : embedding element ∈ P2 := hedge.1 ▸
          Subgroup.mem_map_of_mem embedding helement
        have hcentral := hstar.1.1.1 himage
        rw [Subgroup.mem_centralizer_iff] at hcentral ⊢
        intro member hmember
        apply hinjective
        have hmem : embedding member ∈ omegaOneCenter S := homega ▸
          Subgroup.mem_map_of_mem embedding hmember
        simpa using hcentral (embedding member) hmem
    have hstartmap : (GAt ctx.Γ ctx.criticalPath.a).map embedding = P1 := by
      rcases hedge with hedge | hedge
      · exact hedge.1
      · have hequal : P1 = P2 := hedge.2.symm.trans hnextmap
        exact hedge.1.trans hequal.symm
    refine ⟨heq, hstartmap, hnextmap, ?_⟩
    rw [show EAt ctx.Γ ctx.criticalPath.firstStep =
      twoResidualIn (GAt ctx.Γ ctx.criticalPath.firstStep) from
        ctx.Γ.twoResidualAt_def ctx.criticalPath.firstStep]
    change SubnormalIn ((twoResidualAmbient _).map embedding) _
    rw [map_twoResidualAmbient_of_subgroup_image _ embedding P2 hnextmap]
    have hstar' : P2 ∈ PStarFamily
        (Subgroup.centralizer (omegaOneCenter (S0 : Subgroup H) : Set H))
        (S0 : Subgroup H) := by simpa only [heq] using hstar
    simpa only [heq, twoResidualIn] using
      pstar_residual_subnormal_in_omegaCentralizer S0 P2 hstar'


public theorem generated_central_first_step_commutator
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    ⁅Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set (P1 ⊔ P2 : Subgroup H)),
      EAt ctx.Γ ctx.criticalPath.a ⊔ twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)⁆ ≤
      QAt ctx.Γ ctx.criticalPath.a := by
  obtain ⟨hglobal, _, _, hsub⟩ := generated_central_first_step_setup ctx hcenter
  let G := (P1 ⊔ P2 : Subgroup H)
  let embedding : G →* H := (P1 ⊔ P2).subtype
  let T := S.subgroupOf (P1 ⊔ P2)
  have hinjective : Function.Injective embedding := (P1 ⊔ P2).subtype_injective
  have hmapS : T.map embedding = S := Subgroup.map_subgroupOf_eq_of_le
    (ctx.hypothesisTwo.fiveOne.P1_mem.1.2.1.1.trans le_sup_left)
  let C := Subgroup.centralizer (omegaOneCenter T : Set G)
  let D := Subgroup.centralizer (omegaOneCenter S : Set H)
  have homega : (omegaOneCenter T).map embedding = omegaOneCenter S := by
    rw [← hmapS]
    exact (omegaOneCenterAmbient_map_injective embedding hinjective T).symm
  have hcent (element : G) : embedding element ∈ D ↔ element ∈ C := by
    change embedding element ∈ Subgroup.centralizer (omegaOneCenter S : Set H) ↔
      element ∈ Subgroup.centralizer (omegaOneCenter T : Set G)
    rw [← homega]
    simp only [Subgroup.mem_centralizer_iff]
    constructor
    · intro h member hmember
      apply hinjective
      simpa using h (embedding member) ⟨member, hmember, rfl⟩
    · intro h member hmember
      obtain ⟨preimage, hpreimage, rfl⟩ := hmember
      simpa using congrArg embedding (h preimage hpreimage)
  let restricted : C →* D :=
    (embedding.comp C.subtype).codRestrict D (fun element ↦ (hcent element).mpr element.property)
  have hlocal : SubnormalIn (EAt ctx.Γ ctx.criticalPath.firstStep) C := by
    refine ⟨fun element helement ↦ (hcent element).mp
      (hsub.1 ⟨element, helement, rfl⟩), ?_⟩
    have hpull := hsub.2.comap restricted
    have heq : (((EAt ctx.Γ ctx.criticalPath.firstStep).map embedding).subgroupOf D).comap
        restricted = (EAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf C := by
      ext element
      change embedding element.val ∈ (EAt ctx.Γ ctx.criticalPath.firstStep).map embedding ↔ _
      constructor
      · rintro ⟨preimage, hpreimage, heq⟩
        have hequal := hinjective heq
        change element.val ∈ EAt ctx.Γ ctx.criticalPath.firstStep
        exact hequal ▸ hpreimage
      · intro hmem
        exact ⟨element.val, hmem, rfl⟩
    rwa [heq] at hpull
  have hrange : (S0 : Subgroup H) ≤ embedding.range := by
    rw [← hglobal, ← hmapS]
    exact Subgroup.map_le_range embedding T
  let sylow := S0.comapOfInjective embedding hinjective hrange
  have hsylow : (sylow : Subgroup G) = T := by
    change (S0 : Subgroup H).comap embedding = T
    rw [← hglobal, ← hmapS,
      Subgroup.comap_map_eq_self_of_injective hinjective]
  have hTC : T ≤ C := Subgroup.le_centralizer_iff.mpr
    ((SevenSix.omegaOneCenter_le_centerAmbient T).trans
      (SevenSix.centerAmbient_le_centralizer T))
  let localSylow := sylow.subtype (hsylow ▸ hTC)
  have hcore : twoCoreIn C ≤ T := by
    have hle := (pCore_isPGroup (G := C) (p := 2)).le_sylow_of_normal localSylow
    rintro element ⟨preimage, hpreimage, rfl⟩
    have hmem := hle hpreimage
    change preimage.val ∈ (sylow : Subgroup G) at hmem
    rwa [hsylow] at hmem
  exact lemma_seven_seven_centralizer_commutator ctx.sectionSeven ctx.Γ ctx.criticalPath
    C rfl hlocal hcore


public theorem generated_central_first_step_center
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    ZAt ctx.Γ ctx.criticalPath.firstStep = omegaOneCenter (S.subgroupOf (P1 ⊔ P2)) := by
  have hsylow := (SevenSix.edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).2
  have hle : omegaOneCenter (S.subgroupOf (P1 ⊔ P2)) ≤
      ZAt ctx.Γ ctx.criticalPath.firstStep := by
    obtain ⟨_, sylow, hsylow⟩ := hsylow
    rw [ZAt, z, ctx.Γ.zAt_def]
    exact le_sSup ⟨sylow, congrArg omegaOneCenter hsylow.symm⟩
  apply z_eq_omega_sylow_of_normal ctx.Γ _ hsylow
  exact normal_of_centralizing _ _ ((Subgroup.map_subtype_le _).trans hsylow.1)
    (Subgroup.le_centralizer_iff.mpr
      ((hle.trans hcenter).trans (SevenSix.centerAmbient_le_centralizer _)))

end Stellmacher.SectionEight
