module
public import Stellmacher.SectionNine.GeneratedContext
public import Stellmacher.SectionFiveToSeven.Result7_7.CentralizerCommutator
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Stellmacher.OmegaOneCenterMap
public import Stellmacher.SectionFiveToSeven.FiveTwoPStarCentralizer
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift


/-!
# Ambient orientation at the initial Section Nine edge

For an ambient Section Nine context, the mapped initial stabilizer is P₁,
the mapped next stabilizer is P₂, and the distinguished two-subgroup is the
ambient Sylow S₀. The next residual is subnormal in the ambient centralizer
of the Sylow omega-center.

By (7.5), that omega-center is central in the next stabilizer, excluding
alternatives (5.1)(a,c). Reversing (5.1)(b) would make the initial center
equal the Sylow omega-center; the (7.4) edge centralizer would then identify
the initial proper two-core with the whole Sylow. Thus (5.1)(b) has the
stated orientation, and the P-star residual theorem gives subnormality.

This shared setup supplies both the ambient centralizer commutator bound
and the source-faithful application of (6.4) in (9.2). Hypothesis Two is
never asserted on the graph group. Source: Stellmacher, Journal of Algebra
190 (1997), (5.1), (5.2), (7.5), and (9.2), printed p.48 / PDF p.38 of
`refs/files/stellmacher-n-group.pdf`.
-/

open Stellmacher Stellmacher.Later Stellmacher.SectionsFiveToSeven
open CosetGraphContext
universe u

private theorem normal_of_centralizing
    {G : Type*} [Group G] (W P : Subgroup G) (hle : W ≤ P)
    (hcent : P ≤ Subgroup.centralizer (W : Set G)) : NormalIn W P := by
  exact ⟨hle, (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
    (hcent.trans (Subgroup.centralizer_le_normalizer (W : Set G)))⟩

public theorem Stellmacher.SectionNine.nine_two_ambient_setup
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {G : Type u} [Group G] [Finite G]
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B) :
    S = (S0 : Subgroup H) ∧
    (GAt ctx.Γ ctx.criticalPath.a).map embedding = P1 ∧
    (GAt ctx.Γ ctx.criticalPath.firstStep).map embedding = P2 ∧
    SubnormalIn ((EAt ctx.Γ ctx.criticalPath.firstStep).map embedding)
      (Subgroup.centralizer (omegaOneCenter S : Set H)) := by
  have hSyl := SevenSix.edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath
  have homega : (omegaOneCenter T).map embedding = omegaOneCenter S := by
    rw [← ctx.map_S]
    exact (omegaOneCenterAmbient_map_injective embedding ctx.embedding_injective T).symm
  have hnext := (lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath
    ctx.commutator_eq).next_center
  have hcentNext : GAt ctx.Γ ctx.criticalPath.firstStep ≤
      Subgroup.centralizer (omegaOneCenter T : Set G) := by
    rw [← hnext.1, hnext.2]
    exact Subgroup.le_centralizer_iff.mpr
      ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
        (SevenSix.centerAmbient_le_centralizer _))
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
    · exact Or.inl ⟨(congrArg (Subgroup.map embedding) hedge.1).trans ctx.map_P1,
        (congrArg (Subgroup.map embedding) hedge.2).trans ctx.map_P2⟩
    · exact Or.inr ⟨(congrArg (Subgroup.map embedding) hedge.1).trans ctx.map_P2,
        (congrArg (Subgroup.map embedding) hedge.2).trans ctx.map_P1⟩
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
        apply ctx.embedding_injective
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
    subst S
    exact pstar_residual_subnormal_in_omegaCentralizer S0 P2 hstar

