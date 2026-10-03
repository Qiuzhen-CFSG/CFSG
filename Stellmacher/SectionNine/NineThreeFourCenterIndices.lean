module
public import Stellmacher.SectionNine.NineThreeMutualOuterIndices
public import Stellmacher.SectionNine.NineThreeFirstRelationsAtSecondNeighbor
public import Stellmacher.SectionNine.NineThreeGeometricCenterIndexFour

/-!
# The four exact center indices in Stellmacher (9.3)(4)

For the two actual geometric extractions, each new center has index two
over its intersection with the other new stabilizer, and that intersection
has index two over the common old-center intersection. The four statements
are expressed as exact cardinality equalities before simultaneous edge
normalization; they retain the actual two new vertices and both old centers.

Restriction of each geometric coatom gives the two outer indices. Reapply
the first center-intersection argument at the second new vertex and use
the second center-intersection argument for the other side. Each inner
index is at most two. If it were one, the two conjugate centers would have
relative index two and the exact geometric edge generation would satisfy
(9.2), forcing their order to be four. Endpoint alignment and local
transitivity contradict that order. Thus both inner indices equal two.

Source: Stellmacher (9.3)(4), Journal of Algebra 190 (1997), p.49,
`refs/files/stellmacher-n-group.pdf`. No change of initial vertex is used
without re-establishing its required center relations.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_three_four_center_indices
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first) :
    let m := ctx.Γ.act first.extraction.x⁻¹ first.l
    let n := ctx.Γ.act second.extraction.x⁻¹ second.l
    Nat.card (ZAt ctx.Γ m) = 2 * Nat.card (ZAt ctx.Γ m ⊓ GAt ctx.Γ n : Subgroup G) ∧
      Nat.card (ZAt ctx.Γ m ⊓ GAt ctx.Γ n : Subgroup G) =
        2 * Nat.card (ZAt ctx.Γ m ⊓ ZAt ctx.Γ first.l : Subgroup G) ∧
      Nat.card (ZAt ctx.Γ n) = 2 * Nat.card (ZAt ctx.Γ n ⊓ GAt ctx.Γ m : Subgroup G) ∧
      Nat.card (ZAt ctx.Γ n ⊓ GAt ctx.Γ m : Subgroup G) =
        2 * Nat.card (ZAt ctx.Γ n ⊓ ZAt ctx.Γ second.l : Subgroup G) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let m := Γ.act first.extraction.x⁻¹ first.l
  let n := Γ.act second.extraction.x⁻¹ second.l
  have houter := nine_three_mutual_outer_indices ctx hb hlarge first second
  have hfirst := nine_three_first_relations_at_second_neighbor ctx hb hlarge first second
  have hsecond := nine_three_second_center_relations ctx hb hlarge first second
  have hcore (v : Γ.Vertex) : QAt Γ v ≤ GAt Γ v := by
    change q Γ v ≤ stabilizer Γ v
    rw [q,Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hI1Y : ZAt Γ m ⊓ ZAt Γ first.l ≤ ZAt Γ m ⊓ GAt Γ n := by
    rw [← hfirst.1]
    exact inf_le_inf_left _ (hcore n)
  have hI2Y : ZAt Γ n ⊓ ZAt Γ second.l ≤ ZAt Γ n ⊓ GAt Γ m := by
    rw [← hsecond.1]
    exact inf_le_inf_left _ (hcore m)
  have hl : first.l ∈ neighborhood Γ cp.a' := by
    rw [first.penultimate]
    exact (nine_three_initial_extraction_inputs ctx.toLocalContext hb).1
  have hVfirst : VAt Γ cp.firstStep ≤ QAt Γ first.l := by
    rw [first.penultimate]
    exact (nine_three_initial_extraction_inputs ctx.toLocalContext hb).2.1
  have hlargeL : 4 < Nat.card (ZAt Γ first.l) := by
    obtain ⟨g,hg,_⟩ := lemma_seven_five_endpoint_alignment ctx.sectionSeven Γ cp ctx.commutator_eq
    have he : Γ.act g cp.a = first.l := hg.trans first.penultimate.symm
    rw [← he]
    change 4 < Nat.card (z Γ (Γ.act g cp.a))
    rw [z_act,Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact hlarge
  have hbound1 : Nat.card (ZAt Γ m ⊓ GAt Γ n : Subgroup G) ≤
      2 * Nat.card (ZAt Γ m ⊓ ZAt Γ first.l : Subgroup G) := by
    rw [← hfirst.1]
    exact hfirst.2.1
  have hi1 := nine_three_geometric_center_index_four ctx cp.a' first.l
    ⟨1,Γ.act_one _⟩ hl (VAt Γ cp.firstStep) first.E first.A0 hVfirst first.actor
    first.extraction hlargeL (ZAt Γ m ⊓ GAt Γ n) hI1Y inf_le_left houter.2 hbound1
  obtain ⟨_,hd,hr,_,hcardR,_⟩ := nine_three_second_center_inputs ctx hb first second
  have hVend : VAt Γ cp.a' ≤ QAt Γ second.l := by
    obtain ⟨_,he⟩ := second.second
    rw [he]
    exact (nine_three_second_extraction_inputs ctx.toLocalContext hb).2.1
  have hlargeR : 4 < Nat.card (ZAt Γ second.l) := by rw [hcardR]; exact hlarge
  have hbound2 : Nat.card (ZAt Γ n ⊓ GAt Γ m : Subgroup G) ≤
      2 * Nat.card (ZAt Γ n ⊓ ZAt Γ second.l : Subgroup G) := by
    rw [← hsecond.1]
    exact hsecond.2.1
  have hi2 := nine_three_geometric_center_index_four ctx cp.firstStep second.l hd hr
    (VAt Γ cp.a') second.E second.A0 hVend second.actor second.extraction hlargeR
    (ZAt Γ n ⊓ GAt Γ m) hI2Y inf_le_left houter.1 hbound2
  exact ⟨houter.2,hi1.1,houter.1,hi2.1⟩

end Stellmacher.SectionNine
