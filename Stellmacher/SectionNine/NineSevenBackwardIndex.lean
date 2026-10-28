module
public import Stellmacher.SectionNine.NineSevenShiftedIntersections
public import Stellmacher.SectionNine.NineSevenNearbyNeighborhoodContraction
public import Stellmacher.SectionNine.NineFivePreviousCommutation
public import Stellmacher.SectionNine.LemmaNineThree

/-!
# The backward module index in Stellmacher (9.7)

The assumed index-two intersection at offsets one and three transports to
an index-two intersection of the terminal module with the module at offset
b minus two. No module cardinality hypothesis is needed.

The middle vertex of each two-arc is in the initial orbit. The proved (9.3)
SL₂(2) quotient acts doubly transitively on its three neighbors, so a graph
action carries the first ordered two-arc to the terminal backward two-arc.
Conjugation covariance of the two modules preserves their intersection and
both finite cardinalities, hence the exact quotient-cardinality relation.

Source: Stellmacher, Journal of Algebra 190 (1997), (9.7), printed p.53,
the initial order-eight reduction, in `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_seven_backward_index_two
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (third : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 3 third)
    (hindex : QuotientCardEq (VAt ctx.Γ ctx.criticalPath.firstStep)
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third) 2)
    (previous : ctx.Γ.Vertex)
    (hprevious : IsCriticalPathOffset ctx.Γ ctx.criticalPath
      (ctx.criticalPath.length - 2) previous) :
    QuotientCardEq (VAt ctx.Γ ctx.criticalPath.a')
      (VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ previous) 2 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlength : 3 ≤ cp.length := by
    obtain ⟨index, hval, _⟩ := hpath
    dsimp [cp]
    omega
  let second := cp.path ⟨2, by omega⟩
  let penultimate := cp.path ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  have hfirstAdj : Γ.adjacent second cp.firstStep := by
    have hedge := cp.path_adj ⟨1, by omega⟩
    change Γ.adjacent (cp.path ⟨1, by omega⟩) second at hedge
    rw [cp.path_first] at hedge
    exact Γ.adjacent_symm hedge
  have hthirdAdj : Γ.adjacent second third := by
    obtain ⟨index, hval, rfl⟩ := hpath
    have hedge := cp.path_adj ⟨2, by omega⟩
    have heq : (⟨2, by omega⟩ : Fin cp.length).succ = index := Fin.ext hval.symm
    exact heq ▸ hedge
  have hfirstDistinct : cp.firstStep ≠ third := by
    intro heq
    have hpos := Nat.card_pos (α := VAt Γ cp.firstStep)
    change Nat.card (VAt Γ cp.firstStep) =
      2 * Nat.card (VAt Γ cp.firstStep ⊓ VAt Γ third : Subgroup G) at hindex
    rw [← heq, inf_idem] at hindex
    omega
  have hterminalAdj : Γ.adjacent penultimate cp.a' :=
    nine_five_penultimate_adjacent ctx.toLocalContext
  have hpreviousAdj : Γ.adjacent penultimate previous := Γ.adjacent_symm
    (nine_five_previous_adjacent_penultimate ctx.toLocalContext hb previous hprevious)
  have htargetDistinct : cp.a' ≠ previous := by
    change IsCriticalPathOffset Γ cp (cp.length - 2) previous at hprevious
    obtain ⟨index, hval, rfl⟩ := hprevious
    have heq : index = ⟨cp.length - 2, by omega⟩ := Fin.ext hval
    rw [heq]
    exact fun h => (nine_seven_path_vertices_ne Γ cp (cp.length - 2)
      cp.length (by omega) le_rfl) (h.symm.trans cp.path_end.symm)
  obtain ⟨secondMover, hsecondMover⟩ :=
    (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.firstStep
      ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj))
      ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hfirstAdj))
  obtain ⟨middleMover, hmiddleMover, _⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have hmiddleOrbit : IsConjugateVertex Γ cp.a penultimate :=
    ⟨middleMover, hmiddleMover⟩
  have horbit : IsConjugateVertex Γ second penultimate := by
    refine ⟨(secondMover : G)⁻¹ * middleMover, ?_⟩
    have hinverse : Γ.act (secondMover : G)⁻¹ second = cp.a := by
      rw [← hsecondMover, ← Γ.act_mul, mul_inv_cancel, Γ.act_one]
    rw [Γ.act_mul, hinverse, hmiddleMover]
  obtain ⟨actor, hleft, _, hright⟩ := nine_seven_two_arc_transport ctx.sectionSeven Γ
    hfirstAdj hthirdAdj hfirstDistinct hterminalAdj hpreviousAdj htargetDistinct
    horbit (lemma_nine_three_ambient ctx hb penultimate hmiddleOrbit).1
  let conjugation := (MulAut.conj actor⁻¹).toMonoidHom
  have hVmap : (VAt Γ cp.firstStep).map conjugation = VAt Γ cp.a' := by
    change (v Γ cp.firstStep).map conjugation = v Γ cp.a'
    rw [← v_act, hleft]
  have hImap : (VAt Γ cp.firstStep ⊓ VAt Γ third : Subgroup G).map conjugation =
      VAt Γ cp.a' ⊓ VAt Γ previous := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj actor⁻¹).injective, hVmap]
    change v Γ cp.a' ⊓ (v Γ third).map conjugation = _
    rw [← v_act, hright]
  have hVcard := Subgroup.card_map_of_injective (f := conjugation) (K := VAt Γ cp.firstStep)
    (MulAut.conj actor⁻¹).injective
  have hIcard := Subgroup.card_map_of_injective (f := conjugation)
    (K := (VAt Γ cp.firstStep ⊓ VAt Γ third : Subgroup G))
    (MulAut.conj actor⁻¹).injective
  rw [hVmap] at hVcard
  rw [hImap] at hIcard
  change Nat.card (VAt Γ cp.a') = 2 * Nat.card (VAt Γ cp.a' ⊓ VAt Γ previous : Subgroup G)
  rw [hVcard, hIcard]
  exact hindex

end Stellmacher.SectionNine
