module

public import Stellmacher.SectionNine.NineTenExtractedCoreExclusion
public import Stellmacher.SectionNine.NineThreeSecondExtractionInputs

/-!
# The second prescribed extraction in (9.10)

Once the first extracted center acts nontrivially and the first-step center
escapes terminal V, that extracted center supplies an actor outside the
first-step core. Apply the geometric extraction to terminal V at the second
path vertex, preserving that actor and the actual residual conjugator.
The returned edge together with the first extracted center generates the
first-step stabilizer: the conjugated terminal module is already in the new
edge, so prescribed-actor generation gives the stronger generating equality.
This also makes the two extracted centers noncommuting. The generic geometric
center exclusion gives the corresponding core noncontainment. The stronger
interface retains the same extracted residual inside its commutator with
the prescribed actor. Geometric extraction changes its conjugator within
that residual but leaves the group and actor unchanged. The original theorem
remains as a statement-preserving wrapper.

Source: Stellmacher (9.10), printed p.57, the second application of (7.8).
No unproved distance bound or shifted critical-pair hypothesis is used here.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem nine_ten_second_extraction_with_actor_commutator
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hnot : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤ VAt ctx.Γ ctx.criticalPath.a')
    (neighbor : ctx.Γ.Vertex)
    (hneighbor : neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a')
    (hcomm : ⁅ZAt ctx.Γ neighbor, VAt ctx.Γ ctx.criticalPath.firstStep⁆ ≠ ⊥) :
    let second := ctx.criticalPath.path ⟨2, by omega⟩
    ∃ (actor : G) (E A0 : Subgroup G)
      (data : NineThreeGeometricData ctx.Γ ctx.criticalPath.firstStep second
        (VAt ctx.Γ ctx.criticalPath.a') E A0 actor),
      actor ∈ ZAt ctx.Γ neighbor ∧
      (GAt ctx.Γ ctx.criticalPath.firstStep ⊓ GAt ctx.Γ (ctx.Γ.act data.x⁻¹ second)) ⊔
        ZAt ctx.Γ neighbor = GAt ctx.Γ ctx.criticalPath.firstStep ∧
      (¬ ZAt ctx.Γ (ctx.Γ.act data.x⁻¹ second) ≤ QAt ctx.Γ neighbor) ∧
      ⁅ZAt ctx.Γ (ctx.Γ.act data.x⁻¹ second), ZAt ctx.Γ neighbor⁆ ≠ ⊥ ∧
      twoResidualIn E ≤ ⁅twoResidualIn E, Subgroup.zpowers actor⁆ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let second := cp.path ⟨2, by dsimp [cp]; omega⟩
  let V := VAt Γ cp.a'
  have hneighborV : ZAt Γ neighbor ≤ V := by
    change ZAt Γ neighbor ≤ VAt Γ cp.a'
    rw [VAt, v, Γ.vAt_def]
    exact le_sSup ⟨neighbor, hneighbor, rfl⟩
  have hnotCore := nine_ten_extracted_center_not_le_first_core ctx hb hnot
    neighbor hneighbor hcomm
  obtain ⟨actor, hactorZ, hactorNot⟩ := Set.not_subset.mp hnotCore
  have hactorV : actor ∈ V := hneighborV hactorZ
  obtain ⟨hsecond, hVcore, _, hPhi⟩ := nine_three_second_extraction_inputs ctx.toLocalContext hb
  have hPhiCore : frattiniAmbient V ≤ QAt Γ cp.firstStep := by
    rw [show frattiniAmbient V = ⊥ from hPhi]
    exact bot_le
  have hVnot : ¬ V ≤ QAt Γ cp.firstStep := fun hle => hactorNot (hle hactorV)
  obtain ⟨conjugator, A0, E, hEP, _, h0A, hgen, hcard, hconjE, _, h0core,
      hedge, hmodel, _, hby, _, hactor0, hactorComm⟩ :=
    sevenEight_quotient_configuration_with_actor_commutator ctx.sectionSeven Γ cp.firstStep second
      hsecond V hVcore hVnot hPhiCore actor hactorV hactorNot
  obtain ⟨data⟩ := nine_three_geometric_extraction ctx.sectionSeven Γ cp.firstStep second
    hsecond V E A0 hVcore hPhiCore actor hactorV hactor0 conjugator hconjE
      hEP hgen h0A hcard h0core hedge hmodel hby
  let next := Γ.act data.x⁻¹ second
  have hreverse : cp.firstStep ∈ neighborhood Γ next :=
    (mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp data.neighbor))
  have hcore : QAt Γ next ≤ GAt Γ cp.firstStep :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core next cp.firstStep hreverse default).2.2
  have hcoreSelf : QAt Γ next ≤ GAt Γ next := by
    rw [QAt, q, Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hconj : V.conjBy data.x ≤ GAt Γ cp.firstStep ⊓ GAt Γ next :=
    data.conjugate_core_le.trans (le_inf hcore hcoreSelf)
  have hneighborGroup : ZAt Γ neighbor ≤ GAt Γ cp.firstStep :=
    hneighborV.trans (lemma_seven_four ctx.sectionSeven Γ cp).reverse_containment.2
  have hgenerate : (GAt Γ cp.firstStep ⊓ GAt Γ next) ⊔ ZAt Γ neighbor =
      GAt Γ cp.firstStep := by
    apply le_antisymm (sup_le inf_le_left hneighborGroup)
    apply data.edge_generated.ge.trans
    refine sup_le ?_ le_sup_left
    rw [data.actor_generated actor hactorV data.actor_outside]
    exact sup_le
      (((Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr hactorZ)).trans le_sup_right)
      (hconj.trans le_sup_left)
  have hneighborReverse : cp.a' ∈ neighborhood Γ neighbor :=
    (mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hneighbor))
  have hZcore : ZAt Γ neighbor ≤ Subgroup.centralizer (QAt Γ neighbor : Set G) :=
    ((lemma_seven_three ctx.sectionSeven Γ).center_core neighbor cp.a' hneighborReverse).trans
      ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))
  refine ⟨actor, E, A0, data, hactorZ, hgenerate, ?_, ?_, hactorComm⟩
  · exact nine_three_geometric_extracted_center_not_le_core ctx.sectionSeven Γ neighbor
      cp.firstStep second V E A0 actor hactorV hactorZ hZcore data
  · intro hbot
    apply neighbor_center_not_normalized ctx.sectionSeven Γ cp.firstStep next data.neighbor
    change GAt Γ cp.firstStep ≤ Subgroup.normalizer (ZAt Γ next : Set G)
    rw [← hgenerate]
    rw [Subgroup.commutator_comm] at hbot
    exact sup_le
      (inf_le_right.trans (stabilizer_le_normalizer_z Γ _))
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot).trans
        (Subgroup.centralizer_le_normalizer _))

/-- The original second-extraction interface. -/
public theorem nine_ten_second_extraction
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hnot : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤ VAt ctx.Γ ctx.criticalPath.a')
    (neighbor : ctx.Γ.Vertex)
    (hneighbor : neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a')
    (hcomm : ⁅ZAt ctx.Γ neighbor, VAt ctx.Γ ctx.criticalPath.firstStep⁆ ≠ ⊥) :
    let second := ctx.criticalPath.path ⟨2, by omega⟩
    ∃ (actor : G) (E A0 : Subgroup G)
      (data : NineThreeGeometricData ctx.Γ ctx.criticalPath.firstStep second
        (VAt ctx.Γ ctx.criticalPath.a') E A0 actor),
      actor ∈ ZAt ctx.Γ neighbor ∧
      (GAt ctx.Γ ctx.criticalPath.firstStep ⊓ GAt ctx.Γ (ctx.Γ.act data.x⁻¹ second)) ⊔
        ZAt ctx.Γ neighbor = GAt ctx.Γ ctx.criticalPath.firstStep ∧
      (¬ ZAt ctx.Γ (ctx.Γ.act data.x⁻¹ second) ≤ QAt ctx.Γ neighbor) ∧
      ⁅ZAt ctx.Γ (ctx.Γ.act data.x⁻¹ second), ZAt ctx.Γ neighbor⁆ ≠ ⊥ := by
  obtain ⟨actor, E, A0, data, hactor, hgenerate, hnotCore, hnoncomm, _⟩ :=
    nine_ten_second_extraction_with_actor_commutator ctx hb hnot
      neighbor hneighbor hcomm
  exact ⟨actor, E, A0, data, hactor, hgenerate, hnotCore, hnoncomm⟩

end Stellmacher.SectionNine
