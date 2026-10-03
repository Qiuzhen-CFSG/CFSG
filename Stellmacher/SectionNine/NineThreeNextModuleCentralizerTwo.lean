module

public import Stellmacher.SectionNine.NineTwoAmbientSetup
public import Stellmacher.SectionFiveToSeven.Result7_7.CentralizerTwo
public import Stellmacher.CharacteristicTwoCoreOvergroup

/-!
# The next-module centralizer in the ambient Section Nine setting

In an ambient Section Nine context, the graph-group centralizer of the
first-step neighbor module is a two-group contained in the first-step core.
The ambient group retains Hypothesis Two; no such hypothesis is imposed
on the embedded graph group.

The Section Nine ambient setup identifies the distinguished Sylow with the
ambient Sylow and places the next residual subnormally in the ambient
omega-centralizer. Pull that subnormality back through the embedding. The
omega-normalizer has characteristic two by Hypothesis One. Its two-core
lies in the Sylow, which centralizes the omega-center, so its omega-centralizer
also has characteristic two. The latter's two-core again lies in the
ambient Sylow, hence in the embedded graph omega-centralizer. Core-overgroup
inheritance and transport therefore give characteristic two of that graph
centralizer. These are exactly the hypotheses of (7.7)(b).

Finally the first-step stabilizer normalizes the module centralizer. Its
Sylow is global, so the two-group centralizer lies in that Sylow by maximality;
normality in the first-step stabilizer then puts it in its two-core.
Source: Stellmacher (7.7)(b), (9.3)(2), Journal of Algebra 190 (1997), pp.36,49,
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext
universe u

private theorem omegaOneCenter_ne_bot_of_isPGroup_52
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (hS : IsPGroup 2 S) (hSne : S ≠ ⊥) :
    omegaOneCenter S ≠ ⊥ := by
  let _ : Nontrivial S :=
    (Subgroup.nontrivial_iff_ne_bot S).2 hSne
  let _ : Nontrivial (Subgroup.center S) := hS.center_nontrivial
  have hcenterP : IsPGroup 2 (Subgroup.center S) :=
    hS.to_subgroup (Subgroup.center S)
  obtain ⟨n, hn, hcard⟩ := hcenterP.nontrivial_iff_card.mp inferInstance
  have htwo : 2 ∣ Nat.card (Subgroup.center S) := by
    rw [hcard]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn)
  have hinner := omega₁_map_subtype_ne_bot
    (G := S) (Subgroup.center S) 2 htwo
  intro hbot
  apply hinner
  apply Subgroup.map_injective (f := S.subtype) S.subtype_injective
  simpa [omegaOneCenter] using hbot

private theorem characteristicTwo_transport
    {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hchar : Subgroup.centralizer (pCore 2 G : Set G) ≤ pCore 2 G) :
    Subgroup.centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
  have hcore := pCore_map_iso 2 e
  intro h hh
  obtain ⟨g, rfl⟩ := e.surjective h
  rw [← hcore]
  apply Subgroup.mem_map_of_mem
  apply hchar
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  apply e.injective
  have hyH : e y ∈ pCore 2 H := by
    rw [← hcore]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hy
  simpa only [map_mul] using Subgroup.mem_centralizer_iff.mp hh (e y) hyH

/-- The next neighbor-module centralizer is a two-group lying in the next
vertex core, with all ambient hypotheses retained on the original group. -/
public theorem nine_three_next_module_centralizer_two
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {G : Type u} [Group G] [Finite G]
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B) :
    IsTwoGroup (Subgroup.centralizer (VAt ctx.Γ ctx.criticalPath.firstStep : Set G)) ∧
      Subgroup.centralizer (VAt ctx.Γ ctx.criticalPath.firstStep : Set G) ≤
        QAt ctx.Γ ctx.criticalPath.firstStep := by
  obtain ⟨hglobal, _, _, hsub⟩ := nine_two_ambient_setup ctx
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
  have hSD : (S0 : Subgroup H) ≤ D := by
    rw [← hglobal]
    exact Subgroup.le_centralizer_iff.mpr
      ((SevenSix.omegaOneCenter_le_centerAmbient S).trans
        (SevenSix.centerAmbient_le_centralizer S))
  let N := Subgroup.normalizer (omegaOneCenter S : Set H)
  have hDN : D ≤ N := Subgroup.centralizer_le_normalizer _
  have hSN : (S0 : Subgroup H) ≤ N := hSD.trans hDN
  have hZp : IsPGroup 2 (omegaOneCenter S) :=
    (S0.isPGroup'.to_le ctx.hypothesisTwo.fiveOne.S_le_S0).to_le
      (Subgroup.map_subtype_le _)
  have hZne : omegaOneCenter S ≠ ⊥ := omegaOneCenter_ne_bot_of_isPGroup_52 S
    (S0.isPGroup'.to_le ctx.hypothesisTwo.fiveOne.S_le_S0)
    ctx.hypothesisTwo.fiveOne.S_nontrivial
  have hNlocal : IsTwoLocal N := ⟨omegaOneCenter S, hZne, hZp, rfl⟩
  have hNchar := (ctx.hypothesisTwo.hyp1.local_solvable_characteristicTwo N hNlocal hSN).2
  have hNcore : (pCore 2 N).map N.subtype ≤ D := by
    have hle := (pCore_isPGroup (G := N) (p := 2)).le_sylow_of_normal (S0.subtype hSN)
    rintro x ⟨xN, hxN, rfl⟩
    exact hSD (hle hxN)
  have hDchar : IsCharacteristicTwoType D :=
    characteristicTwo_of_contains_core_in N D hNchar hDN hNcore
  have hCD : C.map embedding ≤ D := by
    rintro x ⟨c, hc, rfl⟩
    exact (hcent c).mpr hc
  have hDcore : (pCore 2 D).map D.subtype ≤ C.map embedding := by
    have hle := (pCore_isPGroup (G := D) (p := 2)).le_sylow_of_normal (S0.subtype hSD)
    rintro x ⟨xD, hxD, rfl⟩
    have hS : (xD : H) ∈ S := hglobal ▸ hle hxD
    rw [← ctx.map_S] at hS
    obtain ⟨c, hc, heq⟩ := hS
    refine ⟨c, (hcent c).mp ?_, heq⟩
    rw [heq]
    exact xD.property
  have hmapchar : IsCharacteristicTwoType (C.map embedding) :=
    characteristicTwo_of_contains_core_in D (C.map embedding) hDchar hCD hDcore
  have hCchar : IsCharacteristicTwoType C :=
    characteristicTwo_transport (C.equivMapOfInjective embedding ctx.embedding_injective).symm
      hmapchar
  have htwo := lemma_seven_seven_centralizer_two ctx.sectionSeven ctx.Γ ctx.criticalPath
    C rfl hlocal hcore hCchar
  refine ⟨htwo, ?_⟩
  let K := Subgroup.centralizer (VAt ctx.Γ ctx.criticalPath.firstStep : Set G)
  let P := GAt ctx.Γ ctx.criticalPath.firstStep
  have hPK : P ≤ Subgroup.normalizer K :=
    (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.firstStep).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (Subgroup.centralizer_le_normalizer (VAt ctx.Γ ctx.criticalPath.firstStep : Set G))).mp
          (Subgroup.normal_subgroupOf_centralizer_normalizer _))
  have hTP : T ≤ P := (SevenSix.edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).2.1
  have hKT : K ≤ T := by
    have hmax := sylow.is_maximal'
      (sylow.isPGroup'.to_sup_of_normal_right' htwo
        ((hsylow.le.trans hTP).trans hPK)) le_sup_left
    exact (le_sup_right.trans hmax.le).trans hsylow.le
  have hKP : K ≤ P := hKT.trans hTP
  have hKnormal : (K.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKP).mpr hPK
  have hKp : IsPGroup 2 (K.subgroupOf P) :=
    htwo.of_equiv (Subgroup.subgroupOfEquivOfLe hKP).symm
  have hKcore : K.subgroupOf P ≤ pCore 2 P := le_sSup ⟨hKnormal, hKp⟩
  change K ≤ q ctx.Γ ctx.criticalPath.firstStep
  rw [q, ctx.Γ.twoCoreAt_def]
  rw [← Subgroup.map_subgroupOf_eq_of_le hKP]
  exact Subgroup.map_mono hKcore

end Stellmacher.SectionNine
