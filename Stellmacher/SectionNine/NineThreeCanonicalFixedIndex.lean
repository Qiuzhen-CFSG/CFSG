module
public import Stellmacher.SectionNine.NineThreeNormalizedGeometry
public import Stellmacher.SectionNine.NineThreeFourCenterIndices
public import Stellmacher.SectionNine.NineThreeCanonicalFixedGeneration

/-!
# The geometric index-four bound for canonical fixed vectors

Assume only that the canonical barred critical subgroup is nontrivial in the
actual ambient Section Nine context. A vector of the initial center fixed by
its entire canonical preimage is subject directly to (6.4). No identification
with the native Baumann subgroup or nontrivial native Thompson action is needed.

For the normalized second extraction, its module and actual residual
conjugate lie in the old and new cores, so the extracted group centralizes
the two-center overlap. Its edge generation and the canonical fixed-vector
consequence of (6.4) put the overlap of its old center with the canonical
fixed subgroup into the next center. The exact four-index theorem, transported
through the actual normalization, bounds the fixed subgroup by four times
that next center. The fixed subgroup is the literal ambient-preimage pullback.

This proves the fixed-space implication used in Stellmacher (9.3), Journal
of Algebra 190 (1997), p.50, `refs/files/stellmacher-n-group.pdf`, directly
for the barred subgroup of (6.4). It also covers a trivial native Thompson
image when the canonical action still has a nontrivial offender.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem geometric_canonical_fixed_center
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hJ : sectionSixBarredCritical ctx.hypothesisTwo ≠ ⊥)
    (r : ctx.Γ.Vertex) (hr : r ∈ neighborhood ctx.Γ ctx.criticalPath.firstStep)
    (V E A0 : Subgroup G) (hVQ : V ≤ QAt ctx.Γ r) (actor : G)
    (data : NineThreeGeometricData ctx.Γ ctx.criticalPath.firstStep r V E A0 actor)
    (hnew : ctx.Γ.act data.x⁻¹ r = ctx.criticalPath.a) :
    ZAt ctx.Γ ctx.criticalPath.a ⊓ ZAt ctx.Γ r ⊓
      (Subgroup.centralizer (sectionSixBarredCriticalPreimage ctx.hypothesisTwo : Set H)).comap
        embedding ≤
        ZAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hgenerate : E ⊔ (GAt Γ cp.a ⊓ GAt Γ cp.firstStep) = GAt Γ cp.firstStep := by
    rw [inf_comm]
    rw [← hnew]
    exact data.edge_generated
  have hZr : ZAt Γ r ≤ Subgroup.centralizer (QAt Γ r : Set G) := by
    have hn : cp.firstStep ∈ neighborhood Γ r :=
      (mem_neighborhood_iff_adjacent Γ).mpr
        (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hr))
    exact ((lemma_seven_three ctx.sectionSeven Γ).center_core r cp.firstStep hn).trans
      ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))
  have hZa : ZAt Γ cp.a ≤ Subgroup.centralizer (QAt Γ cp.a : Set G) :=
    ((lemma_seven_three ctx.sectionSeven Γ).center_core cp.a cp.firstStep
      ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)).trans
      ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))
  have hVxQ : V.conjBy data.x ≤ QAt Γ cp.a := by
    rw [← hnew]
    exact data.conjugate_core_le
  have hE : E ≤ Subgroup.centralizer (ZAt Γ cp.a ⊓ ZAt Γ r : Set G) := by
    rw [data.generated]
    exact sup_le
      ((hVQ.trans (Subgroup.le_centralizer_iff.mp hZr)).trans
        (Subgroup.centralizer_le inf_le_right))
      ((hVxQ.trans (Subgroup.le_centralizer_iff.mp hZa)).trans
        (Subgroup.centralizer_le inf_le_left))
  intro w hw
  exact nine_three_canonical_fixed_generation ctx hJ E hgenerate w hw.1.1 hw.2
    ((Subgroup.le_centralizer_iff.mp hE) hw.1)

private theorem card_le_mul_of_intersection
    {G : Type*} [Group G] [Finite G] (V I F Z : Subgroup G)
    (hFV : F ≤ V) (hVI : Nat.card V = 4 * Nat.card (V ⊓ I : Subgroup G))
    (hfixed : F ⊓ I ≤ Z) : Nat.card F ≤ 4 * Nat.card Z := by
  have hv := ((V ⊓ I).subgroupOf V).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (show V ⊓ I ≤ V from inf_le_left)).toEquiv] at hv
  change (V ⊓ I).relIndex V * Nat.card (V ⊓ I : Subgroup G) = Nat.card V at hv
  rw [Subgroup.inf_relIndex_left] at hv
  have hi : I.relIndex V = 4 := Nat.eq_of_mul_eq_mul_right Nat.card_pos (hv.trans hVI)
  have hle : I.relIndex F ≤ 4 := by
    rw [← hi]
    exact Subgroup.relIndex_le_of_le_right hFV (by rw [hi]; decide)
  have hf := ((F ⊓ I).subgroupOf F).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (show F ⊓ I ≤ F from inf_le_left)).toEquiv] at hf
  change (F ⊓ I).relIndex F * Nat.card (F ⊓ I : Subgroup G) = Nat.card F at hf
  rw [Subgroup.inf_relIndex_left] at hf
  rw [← hf]
  exact Nat.mul_le_mul hle (Nat.card_le_card_of_injective (Subgroup.inclusion hfixed)
    (Subgroup.inclusion_injective hfixed))

public theorem nine_three_canonical_fixed_index_graph
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second)
    (hJ : sectionSixBarredCritical ctx.hypothesisTwo ≠ ⊥) :
    Nat.card (ZAt ctx.Γ ctx.criticalPath.a ⊓
      (Subgroup.centralizer (sectionSixBarredCriticalPreimage ctx.hypothesisTwo : Set H)).comap
        embedding : Subgroup G) ≤ 4 * Nat.card (ZAt ctx.Γ ctx.criticalPath.firstStep) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let c := MulAut.conj config.g⁻¹
  let r := Γ.act config.g second.l
  let n0 := Γ.act second.extraction.x⁻¹ second.l
  have hr : r ∈ neighborhood Γ cp.firstStep := by
    obtain ⟨_,_,hn,_,_,_⟩ := nine_three_second_center_inputs ctx hb first second
    rw [← config.fixes_firstStep]
    exact (mem_neighborhood_iff_adjacent Γ).mpr
      (adjacent_act Γ config.g ((mem_neighborhood_iff_adjacent Γ).mp hn))
  have hVQ : VAt Γ (Γ.act config.g cp.a') ≤ QAt Γ r := by
    have hv : VAt Γ cp.a' ≤ QAt Γ second.l := by
      obtain ⟨_,he⟩ := second.second
      rw [he]
      exact (nine_three_second_extraction_inputs ctx.toLocalContext hb).2.1
    change v Γ (Γ.act config.g cp.a') ≤ q Γ (Γ.act config.g second.l)
    rw [v_act,q_act]
    exact Subgroup.map_mono hv
  have hfixed := geometric_canonical_fixed_center ctx hJ r hr
    (VAt Γ (Γ.act config.g cp.a'))
    (second.E.map c.toMonoidHom) (second.A0.map c.toMonoidHom) hVQ
    (c second.actor) config.second_geometry config.second_new_vertex
  have hZnmap : (ZAt Γ n0).map c.toMonoidHom = ZAt Γ cp.a := by
    change (z Γ n0).map (MulAut.conj config.g⁻¹).toMonoidHom = _
    rw [← z_act,config.maps_new_vertex]
  have hZrmap : (ZAt Γ second.l).map c.toMonoidHom = ZAt Γ r := by
    change (z Γ second.l).map (MulAut.conj config.g⁻¹).toMonoidHom = _
    rw [← z_act]
  have hc := nine_three_four_center_indices ctx hb hlarge first second
  have hcardold : Nat.card (ZAt Γ n0) =
      4 * Nat.card (ZAt Γ n0 ⊓ ZAt Γ second.l : Subgroup G) := by
    rw [hc.2.2.1,hc.2.2.2]
    change 2 * (2 * Nat.card (ZAt Γ n0 ⊓ ZAt Γ second.l : Subgroup G)) = _
    omega
  have hcard : Nat.card (ZAt Γ cp.a) =
      4 * Nat.card (ZAt Γ cp.a ⊓ ZAt Γ r : Subgroup G) := by
    rw [← hZnmap,← hZrmap,← Subgroup.map_inf _ _ _ c.injective,
      Subgroup.card_map_of_injective c.injective,Subgroup.card_map_of_injective c.injective]
    exact hcardold
  apply card_le_mul_of_intersection (ZAt Γ cp.a) (ZAt Γ r) _ _ inf_le_left hcard
  intro w hw
  exact hfixed ⟨⟨hw.1.1,hw.2⟩,hw.1.2⟩

end Stellmacher.SectionNine
