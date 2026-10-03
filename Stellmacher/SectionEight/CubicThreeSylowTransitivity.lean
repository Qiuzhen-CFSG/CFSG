module

public import Stellmacher.SectionNine.CubicLocalAction

/-!
# Three-Sylow transitivity on cubic neighborhoods

A three-Sylow of the vertex stabilizer has order divisible by three,
because the stabilizer surjects onto the six-element group `SL₂(2)`.
Its intersection with each incident edge stabilizer is trivial: the edge
has twice the order of the two-core and is therefore a two-group.
The orbit map is injective into the three-element neighborhood, hence
surjective. This uses genuine Sylow data and the graph’s right action.

Source: Stellmacher, printed pp.41–42 (PDF pp.31–32), the setup and proof
of (8.6), in `refs/files/stellmacher-n-group.pdf`.
-/

open scoped Pointwise

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem cubic_three_sylow_transitive
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (d : graph.Vertex)
    (hmodel : QuotientIsModel (GAt graph d) (QAt graph d) SL2Two)
    (T : Subgroup G) (hT : IsSylowIn 3 T (GAt graph d)) :
    IsActionTransitiveOn graph T (neighborhood graph d) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : Finite graph.Vertex := graph.finiteVertex
  have hlocal := SectionNine.cubic_local_action_of_sl2Two_quotient graph hyp d hmodel
  obtain ⟨sylow, hsylow⟩ := hT
  have hTle : T ≤ GAt graph d := by
    rw [← hsylow]
    exact Subgroup.map_subtype_le _
  have hTp : IsPGroup 3 T := by
    rw [← hsylow]
    exact sylow.isPGroup'.map _
  have hdiv : 3 ∣ Nat.card T := by
    have hdivLocal : 3 ∣ Nat.card (GAt graph d) := by
      obtain ⟨projection, hsurj, _⟩ := hmodel
      have hquot := projection.ker.index_mul_card
      rw [Subgroup.index_ker, projection.range_eq_top_of_surjective hsurj,
        Subgroup.card_top,
        SectionOne.RankOneThreeGroupAssembly.isSL2Two_card
          (show IsSL2Two SL2Two from ⟨MulEquiv.refl _⟩)] at hquot
      omega
    have hdivSylow := sylow.dvd_card_of_dvd_card hdivLocal
    rw [← hsylow, Nat.card_congr
      (Subgroup.equivMapOfInjective (sylow : Subgroup (GAt graph d))
        (GAt graph d).subtype (GAt graph d).subtype_injective).toEquiv.symm]
    exact hdivSylow
  have hTcard : 3 ≤ Nat.card T := Nat.le_of_dvd Nat.card_pos hdiv
  intro first second hfirst hsecond
  have hfirstAdj := (SevenSix.mem_neighborhood_iff_adjacent graph).mp hfirst
  have hsecondAdj := (SevenSix.mem_neighborhood_iff_adjacent graph).mp hsecond
  have hedgep : IsPGroup 2 ↥(GAt graph d ⊓ GAt graph first) := by
    have hcorep : IsPGroup 2 (QAt graph d) := by
      change IsPGroup 2 (graph.twoCoreAt d)
      rw [graph.twoCoreAt_def]
      exact (pCore_isPGroup (p := 2) (G := GAt graph d)).map (GAt graph d).subtype
    obtain ⟨power, hpower⟩ := IsPGroup.iff_card.mp hcorep
    apply IsPGroup.of_card (n := power + 1)
    rw [show Nat.card ↥(GAt graph d ⊓ GAt graph first) =
      2 * Nat.card (QAt graph d) from hlocal.edge_card first hfirstAdj,
      hpower, pow_succ, mul_comm]
  have hdisjoint : Disjoint T (GAt graph d ⊓ GAt graph first) :=
    hTp.disjoint_of_coprime hedgep (by decide)
  have hfix (actor : G) : actor ∈ GAt graph d ↔ graph.act actor d = d :=
    Set.ext_iff.mp (graph.stabilizer_def d) actor
  let orbitMap : T → {neighbor // graph.adjacent d neighbor} := fun actor =>
    ⟨graph.act (actor : G) first, by
      have hadj := adjacent_act graph (actor : G) hfirstAdj
      rwa [(hfix actor).mp (hTle actor.property)] at hadj⟩
  have hinj : Function.Injective orbitMap := by
    intro actor other heq
    have hact : graph.act (actor : G) first = graph.act (other : G) first :=
      congrArg Subtype.val heq
    have hratioT : (actor : G) * (other : G)⁻¹ ∈ T :=
      T.mul_mem actor.property (T.inv_mem other.property)
    have hratioEdge : (actor : G) * (other : G)⁻¹ ∈
        GAt graph d ⊓ GAt graph first := by
      refine ⟨hTle hratioT, ?_⟩
      apply (Set.ext_iff.mp (graph.stabilizer_def first) _).mpr
      change graph.act ((actor : G) * (other : G)⁻¹) first = first
      rw [graph.act_mul, hact, ← graph.act_mul, mul_inv_cancel, graph.act_one]
    have hratio := Subgroup.disjoint_def.mp hdisjoint hratioT hratioEdge
    exact Subtype.ext (mul_inv_eq_one.mp hratio)
  have hsurj := (hinj.bijective_of_nat_card_le (by
    rw [hlocal.degree]
    exact hTcard)).surjective
  obtain ⟨actor, hactor⟩ := hsurj ⟨second, hsecondAdj⟩
  exact ⟨actor, congrArg Subtype.val hactor⟩

end Stellmacher.SectionEight

