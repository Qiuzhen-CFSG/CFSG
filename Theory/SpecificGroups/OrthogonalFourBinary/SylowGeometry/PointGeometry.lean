module

public import Theory.SpecificGroups.OrthogonalFourBinary.SylowGeometry.Omega
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# Singular-point and singular-line stabilizers

A Sylow two-subgroup fixes one of the nine nonzero singular vectors, whose
stabilizer has order eight. A singular-line stabilizer has order twelve.
The finite coordinate calculation shows that an intersection of order four
forces incidence, and is exactly the Ω-part of the point stabilizer. Its
elements square to one and it contains an interchange of the definite planes.
All certificates use the bijection with actual isometries from Coordinates.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.66(1)--(3),
printed p.1152, with the space of pp.1121--1122.
-/

@[expose] public section

open Subgroup Theory.AlgebraicGroup
namespace OrthogonalFourBinary.SylowGeometry
open TerminalLines
set_option synthInstance.maxSize 10000
abbrev Actor := OrthogonalFourBinary.IsometryGroup

def preservesGraph (k : Code) (i : LineCode) : Prop :=
  ∀ x : Space, (eval k x).2 = planeEval i (eval k x).1 ↔ x.2 = planeEval i x.1
instance (k : Code) (i : LineCode) : Decidable (preservesGraph k i) :=
  inferInstanceAs (Decidable (∀ _x : Space, _))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem finite_line_card : ∀ i : LineCode,
    Fintype.card {k : Code // preservesGraph k i} = 12 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem finite_point_line : ∀ x : Space, x ≠ 0 → q x = 0 → ∀ i : LineCode,
    4 ≤ Fintype.card {k : Code // eval k x = x ∧ preservesGraph k i} →
      x.2 = planeEval i x.1 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem finite_intersection : ∀ x : Space, x ≠ 0 → q x = 0 → ∀ i : LineCode,
    x.2 = planeEval i x.1 → ∀ k : Code, eval k x = x →
      (preservesGraph k i ↔ k.1.2 = k.2.1.2) := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem finite_square : ∀ x : Space, x ≠ 0 → q x = 0 → ∀ k : Code,
    eval k x = x → k.1.2 = k.2.1.2 → ∀ v : Space, eval k (eval k v) = v := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem finite_interchange : ∀ x : Space, x ≠ 0 → q x = 0 →
    ∃ k : Code, eval k x = x ∧ k.1.2 = k.2.1.2 ∧ k.2.2 = true := by decide +kernel


theorem codeMap_mem_line (k : Code) (i : LineCode) :
    codeMap k ∈ lineStabilizer (graphLine i) ↔ preservesGraph k i := by
  change (∀ x : Space, (candidate k x).2 = planePermutation i (candidate k x).1 ↔
    x.2 = planePermutation i x.1) ↔ _
  simp only [candidate_eval, planePermutation_eval]
  rfl

theorem graph_stabilizer_card (i : LineCode) : Nat.card (lineStabilizer (graphLine i)) = 12 := by
  let e : {k : Code // preservesGraph k i} ≃ lineStabilizer (graphLine i) :=
    codeEquiv.subtypeEquiv (fun k => (codeMap_mem_line k i).symm)
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, finite_line_card]

theorem singular_line_stabilizer_card (E : Subgroup (Multiplicative Space))
    (hcard : Nat.card E = 4) (hs : ∀ v ∈ E, form v.toAdd = 0) :
    Nat.card (lineStabilizer E) = 12 := by
  obtain ⟨i,rfl⟩ := singular_four_eq_graph E hcard hs
  exact graph_stabilizer_card i

private abbrev Point := {x : Space // x ≠ 0 ∧ form x = 0}
private instance : MulAction Actor Point where
  smul e x := ⟨e.val x, by
    constructor
    · intro h
      exact x.property.1 (e.val.injective (h.trans (map_zero e.val).symm))
    · exact ((mem_quadraticIsometrySubgroup form _).mp e.property x).trans x.property.2⟩
  one_smul _ := Subtype.ext rfl
  mul_smul _ _ _ := Subtype.ext rfl

/-- Every Sylow two-subgroup is the stabilizer of a nonzero singular vector. -/
theorem sylow_eq_point_stabilizer (P : Sylow 2 Actor) :
    ∃ x : Space, x ≠ 0 ∧ form x = 0 ∧ (P : Subgroup Actor) = MulAction.stabilizer Actor x := by
  have hc : Nat.card Point = 9 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  obtain ⟨x,hx⟩ := P.isPGroup'.nonempty_fixed_point_of_prime_not_dvd_card Point
    (by rw [hc]; decide)
  have hP : (P : Subgroup Actor) ≤ MulAction.stabilizer Actor x.val := by
    intro g hg
    exact congrArg Subtype.val (hx ⟨g,hg⟩)
  have he := P.is_maximal' (IsPGroup.of_card (n := 3)
    (IndexTwoNormalizer.singular_stabilizer_card x.val x.property.1 x.property.2)) hP
  exact ⟨x.val,x.property.1,x.property.2,he.symm⟩

/-- A point stabilizer meets a singular-line stabilizer in four elements only
when the point lies on the line; the intersection is then exactly its Ω-part. -/
theorem point_line_intersection (x : Space) (hx : x ≠ 0) (hqx : form x = 0)
    (i : LineCode)
    (hc : Nat.card (MulAction.stabilizer Actor x ⊓ lineStabilizer (graphLine i) :
      Subgroup Actor) = 4) :
    MulAction.stabilizer Actor x ⊓ lineStabilizer (graphLine i) =
      MulAction.stabilizer Actor x ⊓ omega := by
  let e : {k : Code // eval k x = x ∧ preservesGraph k i} ≃
      (MulAction.stabilizer Actor x ⊓ lineStabilizer (graphLine i) : Subgroup Actor) :=
    codeEquiv.subtypeEquiv (fun k => by
      change (eval k x = x ∧ preservesGraph k i) ↔
        (candidate k x = x ∧ codeMap k ∈ lineStabilizer (graphLine i))
      rw [candidate_eval, codeMap_mem_line])
  have hcount : Fintype.card {k : Code // eval k x = x ∧ preservesGraph k i} = 4 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr e, hc]
  have hxi := finite_point_line x hx hqx i (by omega)
  ext g
  obtain ⟨k,rfl⟩ := codeMap_bijective.surjective g
  change (candidate k x = x ∧ codeMap k ∈ lineStabilizer (graphLine i)) ↔
    (candidate k x = x ∧ codeMap k ∈ omega)
  rw [candidate_eval, codeMap_mem_line, codeMap_mem_omega]
  exact and_congr_right (fun hk => finite_intersection x hx hqx i hxi k hk)

/-- The Ω-part of a singular-point stabilizer has exponent dividing two. -/
theorem point_omega_square (x : Space) (hx : x ≠ 0) (hqx : form x = 0)
    (g : Actor) (hg : g ∈ MulAction.stabilizer Actor x ⊓ omega) : g ^ 2 = 1 := by
  obtain ⟨k,rfl⟩ := codeMap_bijective.surjective g
  have hfix : eval k x = x := (candidate_eval k x).symm.trans hg.1
  have hk := (codeMap_mem_omega k).mp hg.2
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change candidate k (candidate k v) = v
  rw [candidate_eval, candidate_eval]
  exact finite_square x hx hqx k hfix hk v

/-- The Ω-part of every singular-point stabilizer contains a plane interchange. -/
theorem exists_point_omega_interchange (x : Space) (hx : x ≠ 0) (hqx : form x = 0) :
    ∃ k : Code, codeMap k ∈ MulAction.stabilizer Actor x ⊓ omega ∧ k.2.2 = true := by
  obtain ⟨k,hfix,hpar,hswap⟩ := finite_interchange x hx hqx
  refine ⟨k,⟨?_,(codeMap_mem_omega k).mpr hpar⟩,hswap⟩
  change candidate k x = x
  rw [candidate_eval, hfix]

end OrthogonalFourBinary.SylowGeometry
