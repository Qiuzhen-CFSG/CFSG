module

public import Stellmacher.SectionNine.NineThreeInitialExtractionInputs
public import Stellmacher.SectionNine.NineThreeExtractedCenterNoncontainment
public import Stellmacher.SectionNine.NineThreeGeometricCenterIntersections
public import Stellmacher.SectionFiveToSeven.Result7_8.GeometricExtraction

/-!
# Initial geometric extraction for Stellmacher (9.10)

The first application of (7.8) to the neighbor-center join at the initial
step produces an actual neighbor of the terminal vertex. Its stabilizer
cuts that join with index two and generates the terminal stabilizer with
the join. The initial center escapes the extracted stabilizer, while the
extracted center escapes the initial core. The same choice retains generation
by its core and the old edge, and its center acts nontrivially on the module.

Critical minimality supplies the actor module in the penultimate core.
The prescribed-actor quotient configuration and geometric extraction keep
the actual residual conjugator. Its conjugated module lies in the new
core, so the recorded generation by E reduces to generation by the original
module and the new edge. The prescribed initial-center actor gives the
first exclusion; the proved geometric core-exclusion lemma gives the second.
The strongest interface retains this entire geometric data packet and the
residual commutator bound for every actor outside its coatom. This lets later
normalization keep the actual first conjugator and select its support using
the normalized transvection. Earlier interfaces remain wrappers. The core-edge
generation theorem retains the other generating equation. If
the extracted center commuted with the module, generation would make the
whole terminal stabilizer normalize that center, contradicting the shared
neighbor-center normalizer obstruction.

These assertions use only Section Nine's local context, which any genuine
ambient context supplies without transferring Hypothesis Two to the graph
group. They do not prove the later center noncontainments or the terminal
distance bound. The geometric argument also applies when the distance is
three, so the extraction uses the weaker, sufficient hypothesis b > 1.

Source: Stellmacher, Journal of Algebra 190 (1997), (9.10), printed p.57 /
PDF p.47 of `refs/files/stellmacher-n-group.pdf`, first application of (7.8).
The full proof of (9.10) continues through printed p.59.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem nine_ten_geometric_edge_generation
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (h : SectionSevenHypotheses G T A B)
    (Γ : CosetGraphContext G T A B) (vertex neighbor : Γ.Vertex)
    (V E A0 : Subgroup G) (actor : G)
    (data : NineThreeGeometricData Γ vertex neighbor V E A0 actor) :
    (GAt Γ vertex ⊓ GAt Γ (Γ.act data.x⁻¹ neighbor)) ⊔ V =
      GAt Γ vertex := by
  let extracted := Γ.act data.x⁻¹ neighbor
  have hreverse : vertex ∈ neighborhood Γ extracted :=
    (mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp data.neighbor))
  have hcore : QAt Γ extracted ≤ GAt Γ vertex :=
    ((lemma_seven_three h Γ).sylow_and_core extracted vertex hreverse default).2.2
  have hcoreSelf : QAt Γ extracted ≤ GAt Γ extracted := by
    change Γ.twoCoreAt extracted ≤ Γ.vertexStabilizer extracted
    rw [Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hconj : V.conjBy data.x ≤ GAt Γ vertex ⊓ GAt Γ extracted :=
    data.conjugate_core_le.trans (le_inf hcore hcoreSelf)
  have hVE : V ≤ E := by
    rw [data.generated]
    exact le_sup_left
  apply le_antisymm (sup_le inf_le_left (hVE.trans data.group_le))
  apply data.edge_generated.ge.trans
  refine sup_le ?_ le_sup_left
  exact data.generated.le.trans (sup_le le_sup_right (hconj.trans le_sup_left))

public theorem nine_ten_first_extracted_neighbor_with_residual_witness
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 1 < ctx.criticalPath.length) :
    let penultimate := ctx.criticalPath.path
      ⟨ctx.criticalPath.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
    ∃ neighbor : ctx.Γ.Vertex,
      neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a' ∧
      QuotientCardEq (VAt ctx.Γ ctx.criticalPath.firstStep)
        (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ GAt ctx.Γ neighbor) 2 ∧
      (GAt ctx.Γ ctx.criticalPath.a' ⊓ GAt ctx.Γ neighbor) ⊔
        VAt ctx.Γ ctx.criticalPath.firstStep = GAt ctx.Γ ctx.criticalPath.a' ∧
      QAt ctx.Γ neighbor ⊔
        (GAt ctx.Γ penultimate ⊓ GAt ctx.Γ ctx.criticalPath.a') =
          GAt ctx.Γ ctx.criticalPath.a' ∧
      (¬ ZAt ctx.Γ ctx.criticalPath.a ≤ GAt ctx.Γ neighbor) ∧
      (¬ ZAt ctx.Γ neighbor ≤ QAt ctx.Γ ctx.criticalPath.a) ∧
      ⁅ZAt ctx.Γ neighbor, VAt ctx.Γ ctx.criticalPath.firstStep⁆ ≠ ⊥ ∧
      ∃ (actor : G) (E A0 : Subgroup G)
        (data : NineThreeGeometricData ctx.Γ ctx.criticalPath.a' penultimate
          (VAt ctx.Γ ctx.criticalPath.firstStep) E A0 actor),
        ctx.Γ.act data.x⁻¹ penultimate = neighbor ∧
        ∀ b : G, b ∈ VAt ctx.Γ ctx.criticalPath.firstStep → b ∉ A0 →
          twoResidualIn E ≤ ⁅twoResidualIn E, Subgroup.zpowers b⁆ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let penultimate := cp.path ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let V := VAt Γ cp.firstStep
  obtain ⟨hneighbor, hVcore, _, hPhi, _, _, actor, hactorZ, hactorV, hactorNot⟩ :=
    nine_three_initial_extraction_inputs ctx hb
  have hPhiCore : frattiniAmbient V ≤ QAt Γ cp.a' := by
    rw [show frattiniAmbient V = ⊥ from hPhi]
    exact bot_le
  have hVnot : ¬ V ≤ QAt Γ cp.a' := fun hle => hactorNot (hle hactorV)
  obtain ⟨conjugator, A0, E, hEP, _, h0A, hgen, hcard, hconjE, _, h0core,
      hedge, hmodel, _, hby, _, hactor0, hactors⟩ :=
    sevenEight_quotient_configuration_with_outside_actor_commutators ctx.sectionSeven Γ cp.a' penultimate
      hneighbor V hVcore hVnot hPhiCore actor hactorV hactorNot
  obtain ⟨data⟩ := nine_three_geometric_extraction ctx.sectionSeven Γ cp.a' penultimate
    hneighbor V E A0 hVcore hPhiCore actor hactorV hactor0 conjugator hconjE
      hEP hgen h0A hcard h0core hedge hmodel hby
  refine ⟨Γ.act data.x⁻¹ penultimate, data.neighbor, ?_, ?_, ?_, ?_, ?_, ?_,
    actor, E, A0, data, rfl, hactors⟩
  · change Nat.card V = 2 * Nat.card ↥(V ⊓ GAt Γ (Γ.act data.x⁻¹ penultimate))
    rw [← data.coatom_eq]
    exact data.coatom_card
  · exact nine_ten_geometric_edge_generation ctx.sectionSeven Γ cp.a' penultimate
      V E A0 actor data
  · exact geometric_extraction_core_edge_generation ctx.sectionSeven Γ cp.a' penultimate
      V E A0 actor hVcore data
  · exact fun hle => data.actor_outside (hle hactorZ)
  · exact nine_three_extracted_center_not_le_initial_core ctx cp.a' penultimate
      V E A0 actor hactorV hactorZ data

  · intro hcomm
    apply neighbor_center_not_normalized ctx.sectionSeven Γ cp.a'
      (Γ.act data.x⁻¹ penultimate) data.neighbor
    change GAt Γ cp.a' ≤ Subgroup.normalizer (ZAt Γ (Γ.act data.x⁻¹ penultimate) : Set G)
    rw [← nine_ten_geometric_edge_generation ctx.sectionSeven Γ cp.a' penultimate
      V E A0 actor data]
    rw [Subgroup.commutator_comm] at hcomm
    exact sup_le
      (inf_le_right.trans (stabilizer_le_normalizer_z Γ _))
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
        (Subgroup.centralizer_le_normalizer _))

/-- The original nontrivial-neighbor extraction interface. -/
public theorem nine_ten_first_extracted_neighbor_nontrivial
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 1 < ctx.criticalPath.length) :
    let penultimate := ctx.criticalPath.path
      ⟨ctx.criticalPath.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
    ∃ neighbor : ctx.Γ.Vertex,
      neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a' ∧
      QuotientCardEq (VAt ctx.Γ ctx.criticalPath.firstStep)
        (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ GAt ctx.Γ neighbor) 2 ∧
      (GAt ctx.Γ ctx.criticalPath.a' ⊓ GAt ctx.Γ neighbor) ⊔
        VAt ctx.Γ ctx.criticalPath.firstStep = GAt ctx.Γ ctx.criticalPath.a' ∧
      QAt ctx.Γ neighbor ⊔
        (GAt ctx.Γ penultimate ⊓ GAt ctx.Γ ctx.criticalPath.a') =
          GAt ctx.Γ ctx.criticalPath.a' ∧
      (¬ ZAt ctx.Γ ctx.criticalPath.a ≤ GAt ctx.Γ neighbor) ∧
      (¬ ZAt ctx.Γ neighbor ≤ QAt ctx.Γ ctx.criticalPath.a) ∧
      ⁅ZAt ctx.Γ neighbor, VAt ctx.Γ ctx.criticalPath.firstStep⁆ ≠ ⊥ := by
  obtain ⟨neighbor, hneighbor, hindex, hgenerate, hcore, hinitial, hterminal,
    hnoncomm, _⟩ := nine_ten_first_extracted_neighbor_with_residual_witness ctx hb
  exact ⟨neighbor, hneighbor, hindex, hgenerate, hcore, hinitial, hterminal, hnoncomm⟩

public theorem nine_ten_first_extracted_neighbor
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 1 < ctx.criticalPath.length) :
    ∃ neighbor : ctx.Γ.Vertex,
      neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a' ∧
      QuotientCardEq (VAt ctx.Γ ctx.criticalPath.firstStep)
        (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ GAt ctx.Γ neighbor) 2 ∧
      (GAt ctx.Γ ctx.criticalPath.a' ⊓ GAt ctx.Γ neighbor) ⊔
        VAt ctx.Γ ctx.criticalPath.firstStep = GAt ctx.Γ ctx.criticalPath.a' ∧
      (¬ ZAt ctx.Γ ctx.criticalPath.a ≤ GAt ctx.Γ neighbor) ∧
      (¬ ZAt ctx.Γ neighbor ≤ QAt ctx.Γ ctx.criticalPath.a) := by
  obtain ⟨neighbor, hneighbor, hindex, hgenerate, _, hinitial, hterminal, _⟩ :=
    nine_ten_first_extracted_neighbor_nontrivial ctx hb
  exact ⟨neighbor, hneighbor, hindex, hgenerate, hinitial, hterminal⟩

public theorem nine_ten_length_ge_five
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 3 < ctx.criticalPath.length) :
    5 ≤ ctx.criticalPath.length := by
  obtain ⟨half, hhalf⟩ :=
    (lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq).odd_distance
  omega

end Stellmacher.SectionNine
