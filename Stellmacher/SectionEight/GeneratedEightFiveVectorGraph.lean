module

public import Stellmacher.SectionEight.GeneratedEightFiveActionFromFour
public import Stellmacher.QuotientModuleOffenderFixedPoints
public import Stellmacher.SectionFiveToSeven.VertexLocalModule
public import Stellmacher.SectionThree.LocalFamilyGeneratingExtraction

/-!
# Graph prerequisites for the generated fixed-vector criterion

The faithful offender action makes its fixed subgroup proper. Unique local
maximality replaces the full edge by the distinguished Sylow in generation.
The initial center maps to the genuine ambient Section Six module, via the
intrinsic Sylow omega-center and its conjugate closure. These statements use
neither fixed-subgroup normality nor (8.3).

Source: Stellmacher (6.4), (8.4), and (8.5), printed pp.39–40 of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem eight_four_fixed_proper_local
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionEightLocalContext G T A B)
    (w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G))
      (ZAt ctx.Γ ctx.criticalPath.a)) :
    w.oneJFixedPoints T ≠ ZAt ctx.Γ ctx.criticalPath.a := by
  let := w.groupX
  let := w.finiteX
  let := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
  have hnontrivial := (eight_five_offender_local ctx w).2
  intro heq
  apply hnontrivial
  apply bot_unique
  intro actor hactor
  change actor = 1
  apply w.action_injective
  rw [map_one]
  apply MulEquiv.ext
  intro vector
  have hvector : (vector : G) ∈ w.oneJFixedPoints T := heq.ge vector.property
  obtain ⟨fixed, hfixed, hvalue⟩ := Subgroup.mem_map.mp hvector
  have hsame : fixed = vector := Subtype.ext hvalue
  subst fixed
  rw [FixedPoints.mem_subgroup] at hfixed
  exact hfixed ⟨actor, hactor⟩

public theorem eight_four_edge_generation_local
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionEightLocalContext G T A B) (R : Subgroup G)
    (hgenerate : R ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓
      GAt ctx.Γ ctx.criticalPath.firstStep) = GAt ctx.Γ ctx.criticalPath.firstStep) :
    R ⊔ T = GAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let Pa := GAt Γ cp.a
  let P := GAt Γ cp.firstStep
  let D := Pa ⊓ P
  have hlocal := edge_local_data ctx.sectionSeven Γ cp
  have hPa : Pa ∈ PFamily (⊤ : Subgroup G) T := hlocal.1.1
  have hP : P ∈ SectionThree.PSet (⊤ : Subgroup G) T :=
    (pFamily_iff_pSet _ _ _).mp hlocal.2.1
  have hTD : T ≤ D := cp.S_le_edge_stabilizers
  have hjoin : Pa ⊔ P = ⊤ := by
    change stabilizer Γ cp.a ⊔ stabilizer Γ cp.firstStep = ⊤
    rcases cp.edge_stabilizers_are_P with hedge | hedge
    · rw [hedge.1, hedge.2]
      exact ctx.sectionSeven.generated
    · rw [hedge.1, hedge.2, sup_comm]
      exact ctx.sectionSeven.generated
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
    have hQle : Q ≤ pCore 2 G := le_sSup ⟨hQn, hQp⟩
    exact hQne (bot_unique (hQle.trans_eq ctx.sectionSeven.twoCore_eq_bot))
  have hRP : R ≤ P := le_sup_left.trans_eq hgenerate
  by_contra hproper
  obtain ⟨M, hM, hTM, huniq⟩ := hP.2
  have hRTM : R ⊔ T ≤ M.map P.subtype :=
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

public theorem generated_eight_four_center_eq_sectionSixV
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (hmapGa : (GAt ctx.Γ ctx.criticalPath.a).map (P1 ⊔ P2).subtype = P1) :
    (ZAt ctx.Γ ctx.criticalPath.a).map (P1 ⊔ P2).subtype = sectionSixV S P1 := by
  let embedding := (P1 ⊔ P2).subtype
  have hinjective : Function.Injective embedding := (P1 ⊔ P2).subtype_injective
  have hmapS : (S.subgroupOf (P1 ⊔ P2)).map embedding = S :=
    Subgroup.map_subgroupOf_eq_of_le
      (ctx.hypothesisTwo.fiveOne.P1_mem.1.2.1.1.trans le_sup_left)
  let P := GAt ctx.Γ ctx.criticalPath.a
  obtain ⟨_, U, hU⟩ := (edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1
  let f : P →* H := embedding.comp P.subtype
  have hf : Function.Injective f := hinjective.comp P.subtype_injective
  have hUm : (U : Subgroup P).map f = S := by
    rw [show f = embedding.comp P.subtype from rfl, ← Subgroup.map_map, hU, hmapS]
  have hOm : (omegaOneCenterAmbient (U : Subgroup P)).map f = omegaOneCenter S := by
    rw [← omegaOneCenterAmbient_map_injective f hf, hUm]
    rfl
  have hfrange : f.range = P1 := by
    change (embedding.comp P.subtype).range = P1
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hmapGa
  have hlocal := vertexZ_eq_local_vSubgroup ctx.Γ ctx.criticalPath.a U
  change (SectionTwo.vSubgroup U).map P.subtype = ZAt ctx.Γ ctx.criticalPath.a at hlocal
  rw [← hlocal, Subgroup.map_map]
  change (Subgroup.normalClosure
    (omegaOneCenterAmbient (U : Subgroup P) : Set P)).map f = _
  rw [Subgroup.normalClosure, MonoidHom.map_closure, sectionSixV,
    Stellmacher.SectionsFiveToSeven.conjugateClosure]
  congr 1
  ext element
  constructor
  · rintro ⟨preimage, hpreimage, rfl⟩
    obtain ⟨member, hmember, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hpreimage
    obtain ⟨actor, hactor⟩ := isConj_iff.mp hconj
    have hactorMap : f actor ∈ P1 :=
      hfrange.le ⟨actor, rfl⟩
    have hmemberMap : f member ∈ omegaOneCenter S :=
      hOm.le (Subgroup.mem_map_of_mem f hmember)
    refine ⟨⟨f actor, hactorMap⟩, ⟨f member, hmemberMap⟩, ?_⟩
    simpa only [map_mul, map_inv] using (congrArg f hactor).symm
  · rintro ⟨actor, member, rfl⟩
    obtain ⟨actorPreimage, hactor⟩ :=
      (show (actor : H) ∈ f.range from hfrange.ge actor.property)
    obtain ⟨memberPreimage, hmember, hmemberEq⟩ := Subgroup.mem_map.mp (hOm.ge member.property)
    refine ⟨actorPreimage * memberPreimage * actorPreimage⁻¹, ?_, ?_⟩
    · exact Group.mem_conjugatesOfSet_iff.mpr
        ⟨memberPreimage, hmember, isConj_iff.mpr ⟨actorPreimage, rfl⟩⟩
    · simp only [map_mul, map_inv, hactor, hmemberEq]

end Stellmacher.SectionEight
