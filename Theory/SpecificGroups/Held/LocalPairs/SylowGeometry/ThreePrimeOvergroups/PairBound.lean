module

public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.Data
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.PairBound.Witnesses
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.GraphCardBound.Separation

/-!
# Divisibility for the literal Held pair stabilizer

The certified graph refinements bound the last two orbits in the stabilizer
chain at 0,1,2,3 by 256 and 36, and kill the four-point stabilizer. The
Schreier witnesses in `PairBound/Witnesses` supply the full 256-point orbit
and a divisor eighteen at the next level. Thus the three-point stabilizer
has order eighteen or thirty-six, and the two-point stabilizer has order
dividing 256 · 36. Passing to a setwise pair stabilizer adds a divisor of two.

A literal Held word sends the reference pair {0,1} to {447,1337}. Conjugacy
of their actual stabilizers proves the requested divisibility in the fixed
ATLAS carrier. Only preservation of `NormalizerGraph.Adj` is assumed; the
assembly owner discharges that separate generator calculation.

Sources: the unchanged HeG1-p2058B0 permutations, the published `GraphData`
relation and its `GraphCardBound` certificates, and GLS3 Table 5.3p. The
transporter is also recorded in `Held/OddOrderBound.lean`; its two images
are checked here without importing that downstream conditional bound.
-/

open scoped Pointwise
namespace Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups
namespace PairBound
open Held.NormalizerGraph Held.NormalizerGraph.CardBound

private abbrev Stabilizer4 := ↥(MulAction.stabilizer Stabilizer3 (3 : Fin 2058))

private theorem fix1 (g : Stabilizer1) : Fixes 1 g.val.val := by
  intro x hx
  have he : x = 0 := Fin.ext (by omega)
  subst x
  exact g.property

private theorem fix2 (g : Stabilizer2) : Fixes 2 g.val.val.val := by
  intro x hx
  by_cases h : x.val < 1
  · exact fix1 g.val x h
  · have he : x = 1 := Fin.ext (by omega)
    subst x
    exact g.property

private theorem fix3 (g : Stabilizer3) : Fixes 3 g.val.val.val.val := by
  intro x hx
  by_cases h : x.val < 2
  · exact fix2 g.val x h
  · have he : x = 2 := Fin.ext (by omega)
    subst x
    exact g.property

private theorem fix4 (g : Stabilizer4) : Fixes 4 g.val.val.val.val.val := by
  intro x hx
  by_cases h : x.val < 3
  · exact fix3 g.val x h
  · have he : x = 3 := Fin.ext (by omega)
    subst x
    exact g.property

private theorem card_four (hgraph : permutationGroup ≤ preservingGroup) :
    Nat.card Stabilizer4 = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨1, fun g => ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact four_fixed_eq_one _ (hgraph g.val.val.val.val.property) (fix4 g)

private theorem card_three_dvd (hgraph : permutationGroup ≤ preservingGroup) :
    Nat.card Stabilizer3 ∣ 36 := by
  have hu : Nat.card Stabilizer3 ≤ 36 * Nat.card Stabilizer4 :=
    orbit_upper (3 : Fin 2058) (fun x => weight33 x.val)
      (fun g x => invariant33 _ (hgraph g.val.val.val.property) (fix3 g) x) cell3_card.le
  rw [card_four hgraph, mul_one] at hu
  obtain ⟨n, hn⟩ := eighteen_dvd_card_threeStabilizer
  have hp : 0 < Nat.card Stabilizer3 := Nat.card_pos
  have he : Nat.card Stabilizer3 = 18 ∨ Nat.card Stabilizer3 = 36 := by omega
  rcases he with he | he <;> norm_num [he]

private theorem orbit_two_card (hgraph : permutationGroup ≤ preservingGroup) :
    Nat.card (MulAction.orbit Stabilizer2 (2 : Fin 2058)) = 256 := by
  apply Nat.le_antisymm ?_ orbit_two_card_ge
  apply (Nat.card_le_card_of_injective
    (fun x : MulAction.orbit Stabilizer2 (2 : Fin 2058) =>
      (⟨x.val, ?_⟩ : {x : Fin 2058 // weight22 x.val = weight22 2}))
    (fun x y h => Subtype.ext (congrArg
      (fun z : {x : Fin 2058 // weight22 x.val = weight22 2} => z.val) h))).trans cell2_card.le
  obtain ⟨g, hg⟩ := x.property
  rw [← hg]
  exact invariant22 _ (hgraph g.val.val.property) (fix2 g) 2

/-- The pointwise stabilizer of the reference adjacent pair has order dividing 9216. -/
public theorem card_two_dvd (hgraph : permutationGroup ≤ preservingGroup) :
    Nat.card Stabilizer2 ∣ 9216 := by
  have he := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup Stabilizer2 (2 : Fin 2058))
  rw [Nat.card_prod, orbit_two_card hgraph] at he
  rw [← he]
  exact Nat.mul_dvd_mul_left 256 (card_three_dvd hgraph)

private abbrev Pair := ↥(MulAction.stabilizer He ({0, 1} : Set (Fin 2058)))
private abbrev PairZero := ↥(MulAction.stabilizer Pair (0 : Fin 2058))

private theorem pair_mem (g : Pair) (x : Fin 2058) (hx : x ∈ ({0, 1} : Set (Fin 2058))) :
    g.val • x ∈ ({0, 1} : Set (Fin 2058)) := by
  have hm : g.val • x ∈ g.val • ({0, 1} : Set (Fin 2058)) := ⟨x, hx, rfl⟩
  rw [g.property] at hm
  exact hm

private theorem pairZero_fix_one (g : PairZero) : g.val.val • (1 : Fin 2058) = 1 := by
  have h := pair_mem g.val 1 (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h
  · have h0 : g.val.val • (0 : Fin 2058) = 0 := g.property
    have he := (MulAction.injective g.val.val) (h.trans h0.symm)
    norm_num at he
  · exact h

private def pairZeroHom : PairZero →* Stabilizer2 where
  toFun g := ⟨⟨g.val.val, g.property⟩, pairZero_fix_one g⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem pairZeroHom_injective : Function.Injective pairZeroHom := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun g : Stabilizer2 => g.val.val) h

private theorem pair_orbit_dvd_two :
    Nat.card (MulAction.orbit Pair (0 : Fin 2058)) ∣ 2 := by
  have hle : Nat.card (MulAction.orbit Pair (0 : Fin 2058)) ≤ 2 := by
    have hc : Nat.card ({0, 1} : Set (Fin 2058)) = 2 := by
      rw [Nat.card_eq_fintype_card]
      decide +kernel
    rw [← hc]
    apply Nat.card_le_card_of_injective
      (fun x : MulAction.orbit Pair (0 : Fin 2058) =>
        (⟨x.val, ?_⟩ : ({0, 1} : Set (Fin 2058))))
      (fun x y h => Subtype.ext (congrArg
        (fun z : ({0, 1} : Set (Fin 2058)) => z.val) h))
    obtain ⟨g, hg⟩ := x.property
    rw [← hg]
    exact pair_mem g 0 (by simp)
  let : Nonempty (MulAction.orbit Pair (0 : Fin 2058)) :=
    ⟨⟨0, MulAction.mem_orbit_self _⟩⟩
  have hp : 0 < Nat.card (MulAction.orbit Pair (0 : Fin 2058)) := Nat.card_pos
  have he : Nat.card (MulAction.orbit Pair (0 : Fin 2058)) = 1 ∨
      Nat.card (MulAction.orbit Pair (0 : Fin 2058)) = 2 := by omega
  rcases he with he | he <;> norm_num [he]

private theorem card_pair_dvd (hgraph : permutationGroup ≤ preservingGroup) :
    Nat.card Pair ∣ 18432 := by
  have hd : Nat.card PairZero ∣ 9216 :=
    (Subgroup.card_dvd_of_injective pairZeroHom pairZeroHom_injective).trans (card_two_dvd hgraph)
  have he := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup Pair (0 : Fin 2058))
  rw [Nat.card_prod] at he
  rw [← he]
  exact Nat.mul_dvd_mul pair_orbit_dvd_two hd

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

end PairBound

/-- The actual setwise stabilizer in Held of the literal pair `{447,1337}`
has order dividing `2^11 * 3^2`, provided Held preserves the published relation. -/
public theorem pairStabilizer_card_dvd (hgraph : permutationGroup ≤ Held.NormalizerGraph.preservingGroup) :
    Nat.card pairStabilizer ∣ 2 ^ 11 * 3 ^ 2 := by
  have he := Nat.card_congr (MulAction.stabilizerEquivStabilizer PairBound.transporter_pair).toEquiv
  change Nat.card PairBound.Pair = Nat.card pairStabilizer at he
  rw [← he]
  exact PairBound.card_pair_dvd hgraph

end Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups
