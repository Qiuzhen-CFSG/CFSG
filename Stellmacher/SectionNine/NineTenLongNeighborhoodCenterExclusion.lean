module

public import Stellmacher.SectionNine.NineTenDistanceTwoNeighborhood
public import Stellmacher.SectionNine.NineThreeCenterSplitting
public import Stellmacher.SectionNine.NineFivePenultimateResidualGeneration
public import Stellmacher.SectionNine.NineNextVModule

/-!
# Excluding the terminal center from the long distance-two neighborhood

For critical length greater than five, the literal first-step W is abelian
and lies in the preterminal stabilizer. Any predecessor module inside W
therefore centralizes the preterminal center. If the terminal center also
lay in W, that module would centralize both lines of the penultimate center
plane, contrary to its known noncommutation with that plane.

This is the first case exclusion in Stellmacher (9.10)(8), printed p.58,
following (7). The input is the actual predecessor module and its known
noncommutation. Neither the critical path nor an extraction is replaced;
no index or support-displacement assertion is assumed.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_ten_terminal_center_not_le_distance_two_neighborhood
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 5 < ctx.criticalPath.length)
    (predecessor : ctx.Γ.Vertex)
    (hpredecessor : VAt ctx.Γ predecessor ≤
      DistanceTwoNeighborhoodV ctx.Γ ctx.criticalPath.firstStep)
    (hnoncommute : ⁅VAt ctx.Γ predecessor, ZAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)⁆ ≠ ⊥) :
    ¬ ZAt ctx.Γ ctx.criticalPath.a' ≤
      DistanceTwoNeighborhoodV ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let W := DistanceTwoNeighborhoodV Γ cp.firstStep
  let preterminal := cp.path ⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let penultimate := cp.path ⟨cp.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  have hshort : 1 < cp.length := by change 5 < cp.length at hb; omega
  have hgeometry := nine_ten_distance_two_neighborhood_geometry ctx.toLocalContext
    (by change 4 < cp.length; change 5 < cp.length at hb; omega)
  have hpreG : VAt Γ predecessor ≤ GAt Γ preterminal :=
    hpredecessor.trans hgeometry.2.1
  have hpreAdj : Γ.adjacent penultimate preterminal :=
    Γ.adjacent_symm (nine_five_previous_adjacent_penultimate ctx.toLocalContext
      hshort preterminal ⟨⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩,rfl,rfl⟩)
  have hpreOrbit := nine_five_penultimate_neighbor_orbit ctx.toLocalContext preterminal hpreAdj
  have hpreCentral : VAt Γ predecessor ≤ Subgroup.centralizer (ZAt Γ preterminal : Set G) :=
    hpreG.trans (nine_next_center_centralizes_stabilizer ctx.toLocalContext preterminal hpreOrbit)
  intro hterminal
  have htermCentral : VAt Γ predecessor ≤ Subgroup.centralizer (ZAt Γ cp.a' : Set G) :=
    hpredecessor.trans ((Subgroup.le_centralizer_iff_isMulCommutative.mpr
      (hgeometry.2.2.2.2 hb)).trans (Subgroup.centralizer_le hterminal))
  obtain ⟨alignment, halign, _⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have hpenOrbit : IsConjugateVertex Γ cp.a penultimate := ⟨alignment, halign⟩
  have hterminalAdj := nine_five_penultimate_adjacent ctx.toLocalContext
  have hdistinct : cp.a' ≠ preterminal :=
    (nine_five_previous_ne_terminal ctx.toLocalContext hshort preterminal
      ⟨⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩,rfl,rfl⟩).symm
  have hsplit := (nine_three_center_split ctx hshort hpenOrbit
    hterminalAdj hpreAdj hdistinct).1
  apply hnoncommute
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
  apply Subgroup.le_centralizer_iff.mpr
  rw [hsplit]
  exact sup_le (Subgroup.le_centralizer_iff.mp htermCentral)
    (Subgroup.le_centralizer_iff.mp hpreCentral)

end Stellmacher.SectionNine
