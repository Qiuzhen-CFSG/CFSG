module

public import Theory.SpecificGroups.Tits.FirstParabolicPresentation
public import Mathlib.GroupTheory.Index

/-!
# Sylow coordinates and the first-parabolic actor

Parrott's local presentation separates into twenty-one equations in the eight
Sylow generators and seven equations involving the remaining involution. At
Sylow index five, an actor outside the Sylow subgroup and these eight generators
generate the whole local group. This gives a consumer for source constructions
of the Sylow coordinates and their actor; it does not construct either input.

Source: Parrott, “A Characterization of the Tits' Simple Group” (1972), §5,
p.683, equations I--VII with r8 omitted. The exact word conventions are those
of `Tits.R1Presentation`.
-/

public section
namespace Tits.FirstParabolicCoordinates
open Subgroup
variable {H K : Type*} [Group H] [Group K]

@[expose] def r3 (s : Fin 8 → H) : H := s 0 * s 1 * s 2 ^ 2
@[expose] def r5 (s : Fin 8 → H) : H := s 0 * s 4 ^ 2
@[expose] def r7 (s : Fin 8 → H) : H := r3 s * s 2 * s 4 * s 6

/-- The eight source symbols s1,...,s8 and the first Weyl actor r1. -/
@[expose] def assignment (s : Fin 8 → H) (r : H) : ParrottR1Generator → H
  | .r1 => r
  | .s1 => s 0
  | .s2 => s 1
  | .s3 => s 2
  | .s4 => s 3
  | .s5 => s 4
  | .s6 => s 5
  | .s7 => s 6
  | .s8 => s 7

/-- Exactly the twenty-one equations in I--V not involving either Weyl actor. -/
structure SylowRelations (s : Fin 8 → H) : Prop where
  s1_sq : s 0 ^ 2 = 1
  s2_sq : s 1 ^ 2 = 1
  s4_sq : s 3 ^ 2 = 1
  s6_sq : s 5 ^ 2 = 1
  s8_sq : s 7 ^ 2 = 1
  s3_four : s 2 ^ 4 = 1
  s5_four : s 4 ^ 4 = 1
  s7_four : s 6 ^ 4 = 1
  s1_s2 : parrottCommutator (s 0) (s 1) = 1
  s1_s3 : parrottCommutator (s 0) (s 2) = 1
  s1_s5 : parrottCommutator (s 0) (s 4) = 1
  s1_s6 : parrottCommutator (s 0) (s 5) = r3 s
  s1_s7 : parrottCommutator (s 0) (s 6) = s 1 * r3 s * r5 s
  s1_s8 : parrottCommutator (s 0) (s 7) = s 6 ^ 2 * r3 s * s 0
  s2_s4 : parrottCommutator (s 1) (s 3) = 1
  s2_s6 : parrottCommutator (s 1) (s 5) = 1
  s2_s8 : parrottCommutator (s 1) (s 7) = s 3 * s 5
  s7_s2 : parrottCommutator (s 6) (s 1) = s 3 * r5 s
  s7_s4 : parrottCommutator (s 6) (s 3) = r3 s * r5 s
  s3_s5 : parrottCommutator (s 2) (s 4) = s 1 * r3 s * s 3
  s5_s4 : parrottCommutator (s 4) (s 3) = r3 s

/-- Exactly the seven local equations involving r1. No second actor occurs. -/
structure WeylRelations (s : Fin 8 → H) (r : H) : Prop where
  square : r ^ 2 = 1
  five : (s 0 * r) ^ 5 = 1
  s2 : r * s 1 * r = s 7
  s4 : r * s 3 * r = s 5
  s5 : r * s 4 * r = (s 0 * r) ^ 2 * s 4
  s3 : r * s 2 * r = (s 0 * r) ^ 2 * r7 s
  r3 : r * FirstParabolicCoordinates.r3 s * r = s 6 * r7 s

/-- Actual coordinates on the supplied subgroup, including generation there. -/
structure SylowCoordinates (S : Subgroup H) where
  s : Fin 8 → S
  relations : SylowRelations s
  generates : closure (Set.range s) = ⊤

/-- An actor in the original group, outside the supplied subgroup. -/
structure WeylExtension {S : Subgroup H} (d : SylowCoordinates S) where
  element : H
  outside : element ∉ S
  relations : WeylRelations (fun i => (d.s i : H)) element

/-- The scalar equations transport through an actual homomorphism. -/
theorem SylowRelations.map {s : Fin 8 → H} (h : SylowRelations s) (f : H →* K) :
    SylowRelations (fun i => f (s i)) := by
  constructor
  · simpa only [parrottCommutator, r3, r5, r7, map_mul, map_inv, map_pow, map_one]
      using congrArg f h.s1_sq
  · simpa only [parrottCommutator, r3, r5, r7, map_mul, map_inv, map_pow, map_one]
      using congrArg f h.s2_sq
  · simpa only [parrottCommutator, r3, r5, r7, map_mul, map_inv, map_pow, map_one]
      using congrArg f h.s4_sq
  · simpa only [parrottCommutator, r3, r5, r7, map_mul, map_inv, map_pow, map_one]
      using congrArg f h.s6_sq
  · simpa only [parrottCommutator, r3, r5, r7, map_mul, map_inv, map_pow, map_one]
      using congrArg f h.s8_sq
  · simpa only [parrottCommutator, r3, r5, r7, map_mul, map_inv, map_pow, map_one]
      using congrArg f h.s3_four
  · simpa only [parrottCommutator, r3, r5, r7, map_mul, map_inv, map_pow, map_one]
      using congrArg f h.s5_four
  · simpa only [parrottCommutator, r3, r5, r7, map_mul, map_inv, map_pow, map_one]
      using congrArg f h.s7_four
  · simpa only [parrottCommutator, r3, r5, r7, map_mul, map_inv, map_pow, map_one]
      using congrArg f h.s1_s2
  · simpa only [parrottCommutator, r3, r5, r7, map_mul, map_inv, map_pow, map_one]
      using congrArg f h.s1_s3
  · simpa only [parrottCommutator, r3, r5, r7, map_mul, map_inv, map_pow, map_one]
      using congrArg f h.s1_s5
  · simpa only [parrottCommutator, r3, r5, r7, map_mul, map_inv, map_pow, map_one]
      using congrArg f h.s1_s6
  · simpa only [parrottCommutator, r3, r5, r7, map_mul, map_inv, map_pow, map_one]
      using congrArg f h.s1_s7
  · simpa only [parrottCommutator, r3, r5, r7, map_mul, map_inv, map_pow, map_one]
      using congrArg f h.s1_s8
  · simpa only [parrottCommutator, r3, r5, r7, map_mul, map_inv, map_pow, map_one]
      using congrArg f h.s2_s4
  · simpa only [parrottCommutator, r3, r5, r7, map_mul, map_inv, map_pow, map_one]
      using congrArg f h.s2_s6
  · simpa only [parrottCommutator, r3, r5, r7, map_mul, map_inv, map_pow, map_one]
      using congrArg f h.s2_s8
  · simpa only [parrottCommutator, r3, r5, r7, map_mul, map_inv, map_pow, map_one]
      using congrArg f h.s7_s2
  · simpa only [parrottCommutator, r3, r5, r7, map_mul, map_inv, map_pow, map_one]
      using congrArg f h.s7_s4
  · simpa only [parrottCommutator, r3, r5, r7, map_mul, map_inv, map_pow, map_one]
      using congrArg f h.s3_s5
  · simpa only [parrottCommutator, r3, r5, r7, map_mul, map_inv, map_pow, map_one]
      using congrArg f h.s5_s4

/-- The split scalar equations are precisely all twenty-eight local relators. -/
theorem relators {s : Fin 8 → H} {r : H}
    (hs : SylowRelations s) (hr : WeylRelations s r) (i : ParrottR1RelatorIndex) :
    FreeGroup.lift (assignment s r) (parrottR1Relator i) = 1 := by
  cases i <;>
    simp only [parrottR1Relator, parrottR1RelatorInclusion, parrottR1Delete,
      parrottRelator, parrottR3, parrottR5, parrottR7, parrottCommutator,
      map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, assignment, mul_inv_eq_one]
  · exact hr.square
  · exact hs.s1_sq
  · exact hs.s2_sq
  · exact hs.s4_sq
  · exact hs.s6_sq
  · exact hs.s8_sq
  · exact hs.s3_four
  · exact hs.s5_four
  · exact hs.s7_four
  · exact hs.s1_s2
  · exact hs.s1_s3
  · exact hs.s1_s5
  · exact hs.s1_s6
  · exact hs.s1_s7
  · exact hs.s1_s8
  · exact hs.s2_s4
  · exact hs.s2_s6
  · exact hs.s2_s8
  · exact hs.s7_s2
  · exact hs.s7_s4
  · exact hs.s3_s5
  · exact hs.s5_s4
  · exact hr.five
  · exact hr.s2
  · exact hr.s4
  · exact hr.s5
  · exact hr.s3
  · exact hr.r3

/-- Prime index makes the Sylow generators and an outside actor generate the
whole local group. This discharges the generation clause of the presentation. -/
theorem generates {S : Subgroup H} (d : SylowCoordinates S)
    (r : H) (hrS : r ∉ S) (hi : S.index = 5) :
    closure (Set.range (assignment (fun i => (d.s i : H)) r)) = ⊤ := by
  let A := closure (Set.range (assignment (fun i => (d.s i : H)) r))
  have hSA : S ≤ A := by
    have hm := congrArg (Subgroup.map S.subtype) d.generates
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, range_subtype] at hm
    rw [← hm]
    apply (closure_le _).mpr
    rintro _ ⟨s, ⟨i, rfl⟩, rfl⟩
    fin_cases i
    · exact subset_closure ⟨.s1, rfl⟩
    · exact subset_closure ⟨.s2, rfl⟩
    · exact subset_closure ⟨.s3, rfl⟩
    · exact subset_closure ⟨.s4, rfl⟩
    · exact subset_closure ⟨.s5, rfl⟩
    · exact subset_closure ⟨.s6, rfl⟩
    · exact subset_closure ⟨.s7, rfl⟩
    · exact subset_closure ⟨.s8, rfl⟩
  have hr : r ∈ A := subset_closure ⟨.r1, rfl⟩
  have hn : S.relIndex A ≠ 1 := fun h => hrS (relIndex_eq_one.mp h hr)
  have hrel : S.relIndex A = 5 :=
    ((show Nat.Prime 5 by decide).eq_one_or_self_of_dvd _
      (hi ▸ relIndex_dvd_index_of_le hSA)).resolve_left hn
  have hh := relIndex_mul_index hSA
  rw [hrel, hi] at hh
  have hindex : A.index = 1 := by omega
  exact index_eq_one.mp hindex

/-- Construct the exact nine-generator presentation data from local Sylow
coordinates and an outside actor. No generation of H is assumed. -/
def generators {S : Subgroup H} (d : SylowCoordinates S)
    (r : WeylExtension d) (hi : S.index = 5) : FirstParabolicPresentation.Generators H where
  element := assignment (fun i => (d.s i : H)) r.element
  relations := relators (d.relations.map S.subtype) r.relations
  generates := generates d r.element r.outside hi

end Tits.FirstParabolicCoordinates
