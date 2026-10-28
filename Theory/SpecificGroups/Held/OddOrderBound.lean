module

public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.OrbitalPreservation.OrbitUniqueness
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.Data

/-!
# The odd part of Held's order from a pair stabilizer

The defining action is transitive on 2058 points. If it preserves the
published orbital relation, the stabilizer of zero has an orbit of size 425
at one: the existing spanning forest proves reachability, and invariance
proves containment. Orbit–stabilizer therefore expresses the ambient order
as 2058 · 425 times the order of the pointwise stabilizer of zero and one.

A literal word sends this pair to 447 and 1337, checked by kernel reduction
in the original ATLAS carrier. Thus the pointwise stabilizer embeds in the
setwise pair stabilizer already used by the Held three-prime overgroup
calculation. Its divisibility by 2^11 · 3² bounds the ambient odd part by
3³ · 5² · 7³ · 17. The extra power of two is harmless for odd ranks.

Both graph preservation and the pair-stabilizer divisibility remain explicit
premises. This does not assert the exact group order. Sources: the literal
HeG1-p2058B0 tables in `Model/Source`, the published relation in
`Automorphisms/Normalizer/GraphData`, and GLS3 Table 5.3p.
-/

open Subgroup
open scoped Pointwise
namespace Held.OddOrderBound
open NormalizerGraph NormalizerGraph.Orbital
open LocalPairs.SylowGeometry.ThreePrimeOvergroups

private abbrev S1 := Orbital.Stabilizer
private abbrev S2 := ↥(MulAction.stabilizer S1 (1 : Fin 2058))

private theorem orbit_zero : MulAction.orbit He (0 : Fin 2058) = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true]
  obtain ⟨g, hg⟩ := Transitivity.exists_move_zero x
  exact ⟨g, hg⟩

private theorem orbit_one (hgraph : permutationGroup ≤ preservingGroup) :
    MulAction.orbit S1 (1 : Fin 2058) = {x | Adj 0 x} := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    have hg : representation g.val 0 = 0 := g.property
    have h := hgraph g.val.property 0 1
    change Adj (representation g.val 0) (representation g.val 1) ↔ Adj 0 1 at h
    rw [hg] at h
    exact h.mpr (by decide +kernel)
  · intro hx
    obtain ⟨g, hg⟩ := reach x
    rw [(color_row x).mp hx] at hg
    exact ⟨g, hg⟩

private theorem card_factorization (hgraph : permutationGroup ≤ preservingGroup) :
    Nat.card He = 2058 * 425 * Nat.card S2 := by
  have h0 := (Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup He (0 : Fin 2058))).symm
  have h1 := (Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup S1 (1 : Fin 2058))).symm
  rw [Nat.card_prod, orbit_zero, Nat.card_congr (Equiv.Set.univ _), Nat.card_fin] at h0
  rw [Nat.card_prod, orbit_one hgraph] at h1
  change Nat.card S1 = Nat.card {x : Fin 2058 // Adj 0 x} * Nat.card S2 at h1
  rw [row_card] at h1
  change Nat.card He = 2058 * Nat.card S1 at h0
  rw [h0, h1, Nat.mul_assoc]

private def transporter : He :=
  b * b * b * a * b * b * a * b * a * b * a * b * a * b *
    a * b * b * b * a * b * a * b * a * b * b * b * b * b

private theorem transporter_zero : representation transporter 0 = 447 := by decide +kernel
private theorem transporter_one : representation transporter 1 = 1337 := by decide +kernel

private theorem transporter_pair :
    (basePair : Set (Fin 2058)) = transporter • ({0, 1} : Set (Fin 2058)) := by
  rw [Set.smul_set_insert, Set.smul_set_singleton]
  change (basePair : Set (Fin 2058)) = {representation transporter 0, representation transporter 1}
  rw [transporter_zero, transporter_one]
  simp only [basePair, Finset.coe_insert, Finset.coe_singleton]

private def pairHom : S2 →* MulAction.stabilizer He ({0, 1} : Set (Fin 2058)) :=
  (((MulAction.stabilizer He (0 : Fin 2058)).subtype).comp
    (MulAction.stabilizer S1 (1 : Fin 2058)).subtype).codRestrict _ (by
      intro g
      change g.val.val • ({0, 1} : Set (Fin 2058)) = _
      rw [Set.smul_set_insert, Set.smul_set_singleton]
      have h0 : g.val.val • (0 : Fin 2058) = 0 := g.val.property
      have h1 : g.val.val • (1 : Fin 2058) = 1 := g.property
      rw [h0, h1])

private theorem pairHom_injective : Function.Injective pairHom := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  have hh : (pairHom x : He) = (pairHom y : He) := congrArg
    (fun g : MulAction.stabilizer He ({0, 1} : Set (Fin 2058)) => (g : He)) h
  exact hh

/-- The existing pair calculation suffices for the ambient odd-order bound. -/
public theorem card_dvd_of_graph_and_pair_bound
    (hgraph : permutationGroup ≤ preservingGroup)
    (hpair : Nat.card pairStabilizer ∣ 2 ^ 11 * 3 ^ 2) :
    Nat.card He ∣ 2 ^ 12 * (3 ^ 3 * 5 ^ 2 * 7 ^ 3 * 17) := by
  have hd : Nat.card S2 ∣ Nat.card pairStabilizer := by
    let e := MulAction.stabilizerEquivStabilizer transporter_pair
    exact Subgroup.card_dvd_of_injective (e.toMonoidHom.comp pairHom)
      (e.injective.comp pairHom_injective)
  rw [card_factorization hgraph]
  have h := Nat.mul_dvd_mul_left (2058 * 425) (hd.trans hpair)
  convert h using 1
  norm_num

end Held.OddOrderBound
