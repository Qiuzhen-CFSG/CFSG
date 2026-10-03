module

public import Stellmacher.SectionEight.GeneratedContext
public import Stellmacher.SectionEight.GeneratedEightFiveCentralizerSetup
public import Theory.GroupTheory.PGroup.SubnormalCore
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts

/-! # Local vertex-centralizer core control for generated (8.5)

The Sylow hypothesis in the graph group is explicit. The generated application
obtains it from the actual ambient Sylow, not from Hypothesis Two on the join.
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

public theorem eight_five_vertex_centralizer_core_local
    {H : Type*} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (S0 : Sylow 2 H)
    (hglobal : S = (S0 : Subgroup H)) (d : ctx.Γ.Vertex) :
    twoCoreIn (Subgroup.centralizer (ZAt ctx.Γ d : Set H)) ≤ QAt ctx.Γ d := by
  let h := ctx.sectionSeven
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

public theorem eight_five_centralizer_core_control_local
    {H : Type*} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (sylow : Sylow 2 H) (hglobal : S = (sylow : Subgroup H))
    (hz : ZAt ctx.Γ ctx.criticalPath.firstStep = omegaOneCenter S)
    (hsub : SubnormalIn (EAt ctx.Γ ctx.criticalPath.firstStep)
      (Subgroup.centralizer (omegaOneCenter S : Set H)))
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
  dsimp only
  constructor
  · rw [hfirst, hz]
    exact pCoreAmbient_mono_of_isSubnormalIn _ _ 2 hsub.1 hsub.2
  · rw [hlast]
    exact eight_five_vertex_centralizer_core_local ctx sylow hglobal _

private theorem subnormalIn_of_injective_map
    {G H : Type*} [Group G] [Group H]
    (embedding : G →* H) (hinjective : Function.Injective embedding)
    (subgroup : Subgroup G) (ambient : Subgroup H)
    (hsub : SubnormalIn (subgroup.map embedding) ambient) :
    SubnormalIn subgroup (ambient.comap embedding) := by
  refine ⟨fun element helement => hsub.1 ⟨element, helement, rfl⟩, ?_⟩
  let restricted : ambient.comap embedding →* ambient :=
    (embedding.comp (ambient.comap embedding).subtype).codRestrict ambient
      (fun element => element.property)
  have hpull := hsub.2.comap restricted
  have heq : ((subgroup.map embedding).subgroupOf ambient).comap restricted =
      subgroup.subgroupOf (ambient.comap embedding) := by
    ext element
    change embedding element.val ∈ subgroup.map embedding ↔ element.val ∈ subgroup
    constructor
    · rintro ⟨preimage, hpreimage, heq⟩
      exact hinjective heq ▸ hpreimage
    · intro hmem
      exact ⟨element.val, hmem, rfl⟩
  rwa [heq] at hpull

public theorem generated_eight_five_centralizer_core_control
    {H : Type*} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlen : 2 < ctx.criticalPath.length)
    (hfirst : ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ ctx.criticalPath.a'⁆ =
      ZAt ctx.Γ ctx.criticalPath.firstStep)
    (hlast : ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ ctx.criticalPath.a'⁆ =
      ZAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, by omega⟩)) :
    let R := ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ ctx.criticalPath.a'⁆
    let C := Subgroup.centralizer (R : Set (P1 ⊔ P2 : Subgroup H))
    twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep) ≤ twoCoreIn C ∧
      twoCoreIn C ≤
        QAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, by omega⟩) := by
  obtain ⟨hglobal, _, _, hsub⟩ := generated_central_first_step_setup ctx hcenter
  let G := (P1 ⊔ P2 : Subgroup H)
  let embedding : G →* H := (P1 ⊔ P2).subtype
  let T := S.subgroupOf (P1 ⊔ P2)
  have hinjective : Function.Injective embedding := (P1 ⊔ P2).subtype_injective
  have hmapS : T.map embedding = S := Subgroup.map_subgroupOf_eq_of_le
    (ctx.hypothesisTwo.fiveOne.P1_mem.1.2.1.1.trans le_sup_left)
  have homega : (omegaOneCenter T).map embedding = omegaOneCenter S := by
    rw [← hmapS]
    exact (omegaOneCenterAmbient_map_injective embedding hinjective T).symm
  have hcentralizer :
      (Subgroup.centralizer (omegaOneCenter S : Set H)).comap embedding =
        Subgroup.centralizer (omegaOneCenter T : Set G) := by
    ext element
    change embedding element ∈ Subgroup.centralizer (omegaOneCenter S : Set H) ↔ _
    rw [← homega]
    simp only [Subgroup.mem_centralizer_iff]
    constructor
    · intro h member hmember
      apply hinjective
      simpa using h (embedding member) ⟨member, hmember, rfl⟩
    · intro h member hmember
      obtain ⟨preimage, hpreimage, rfl⟩ := hmember
      simpa using congrArg embedding (h preimage hpreimage)
  have hlocalSub := subnormalIn_of_injective_map embedding hinjective _ _ hsub
  rw [hcentralizer] at hlocalSub
  have hrange : (S0 : Subgroup H) ≤ embedding.range := by
    rw [← hglobal, ← hmapS]
    exact Subgroup.map_le_range embedding T
  let sylow := S0.comapOfInjective embedding hinjective hrange
  have hsylow : T = (sylow : Subgroup G) := by
    change T = (S0 : Subgroup H).comap embedding
    rw [← hglobal, ← hmapS, Subgroup.comap_map_eq_self_of_injective hinjective]
  exact eight_five_centralizer_core_control_local ctx.toLocalContext sylow hsylow
    (generated_central_first_step_center ctx hcenter) hlocalSub hlen hfirst hlast

end Stellmacher.SectionEight
