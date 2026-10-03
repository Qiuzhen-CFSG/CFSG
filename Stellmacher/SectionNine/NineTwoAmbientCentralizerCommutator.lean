module
public import Stellmacher.SectionNine.NineTwoAmbientSetup
public import Stellmacher.SectionFiveToSeven.Result7_7.CentralizerCommutator
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Stellmacher.OmegaOneCenterMap
public import Stellmacher.SectionFiveToSeven.FiveTwoPStarCentralizer
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift

/-!
# The ambient-retaining centralizer commutator bound for Section Nine

An ambient Section Nine context gives the initial bound of (7.7)(a), without
any center-cardinality or generating-neighbor assumption. Hypothesis Two
remains on H; the critical path and the conclusion live in the embedded G.
Neither surjectivity of the embedding nor generation of H is assumed.

By (7.5), the next center is both the Sylow omega-center and the next
stabilizer's omega-center. Its image is central, hence normal, in the mapped
next stabilizer, excluding alternatives (5.1)(a),(c). Centralization at the
initial vertex would make its Sylow-center join equal the Sylow omega-center;
the exact edge-centralizer equality (7.4) would then identify its proper
two-core with the whole edge Sylow. This excludes the reversed orientation
of (5.1)(b). Consequently S is the ambient Sylow S0, and the mapped next
stabilizer is the P-star member. The P-star residual theorem, together with
residual functoriality, gives subnormality in the ambient omega-centralizer.

Pull subnormality back along the embedding restricted to omega-centralizers.
Pull S0 back to a Sylow of G, which is exactly T, and restrict it to the local
omega-centralizer. Its normal two-core lies in that Sylow. These are the
genuine hypotheses of the proved centralizer-commutator part of (7.7).
The resulting bound is the input to the final kernel recognition in (9.2).

Source: B. Stellmacher, Journal of Algebra 190 (1997), printed p.48 / PDF p.38,
last sentences of (9.2), with (7.5), (7.7)(a), and the P-star reduction (5.2);
`refs/files/stellmacher-n-group.pdf`.
-/

open Stellmacher Stellmacher.Later Stellmacher.SectionsFiveToSeven
open CosetGraphContext

universe u

private theorem transport_bound
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {G : Type u} [Group G] [Finite G]
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hglobal : S = (S0 : Subgroup H))
    (hsub : SubnormalIn ((EAt ctx.Γ ctx.criticalPath.firstStep).map embedding)
      (Subgroup.centralizer (omegaOneCenter S : Set H))) :
    ⁅Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G),
      EAt ctx.Γ ctx.criticalPath.a ⊔ twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)⁆ ≤
      QAt ctx.Γ ctx.criticalPath.a := by
  let C := Subgroup.centralizer (omegaOneCenter T : Set G)
  let D := Subgroup.centralizer (omegaOneCenter S : Set H)
  have homega : (omegaOneCenter T).map embedding = omegaOneCenter S := by
    rw [← ctx.map_S]
    exact (omegaOneCenterAmbient_map_injective embedding ctx.embedding_injective T).symm
  have hcent (element : G) : embedding element ∈ D ↔ element ∈ C := by
    change embedding element ∈ Subgroup.centralizer (omegaOneCenter S : Set H) ↔
      element ∈ Subgroup.centralizer (omegaOneCenter T : Set G)
    rw [← homega]
    simp only [Subgroup.mem_centralizer_iff]
    constructor
    · intro h member hmember
      apply ctx.embedding_injective
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
        have hequal := ctx.embedding_injective heq
        change element.val ∈ EAt ctx.Γ ctx.criticalPath.firstStep
        exact hequal ▸ hpreimage
      · intro hmem
        exact ⟨element.val, hmem, rfl⟩
    rwa [heq] at hpull
  have hrange : (S0 : Subgroup H) ≤ embedding.range := by
    rw [← hglobal, ← ctx.map_S]
    exact Subgroup.map_le_range embedding T
  let sylow := S0.comapOfInjective embedding ctx.embedding_injective hrange
  have hsylow : (sylow : Subgroup G) = T := by
    change (S0 : Subgroup H).comap embedding = T
    rw [← hglobal, ← ctx.map_S,
      Subgroup.comap_map_eq_self_of_injective ctx.embedding_injective]
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


/-- The full initial centralizer commutator bound, retaining Hypothesis Two
on the original ambient group rather than assuming it on the generated group. -/
public theorem Stellmacher.SectionNine.nine_two_initial_centralizer_commutator
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {G : Type u} [Group G] [Finite G]
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B) :
    ⁅Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G),
      EAt ctx.Γ ctx.criticalPath.a ⊔ twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)⁆ ≤
      QAt ctx.Γ ctx.criticalPath.a := by
  obtain ⟨hglobal, _, _, hsub⟩ := Stellmacher.SectionNine.nine_two_ambient_setup ctx
  exact transport_bound ctx hglobal hsub
