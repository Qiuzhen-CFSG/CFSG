module

public import Theory.SpecificGroups.OrthogonalFourBinary.SylowGeometry.PointGeometry
public import Theory.SpecificGroups.OrthogonalFourBinary.SylowGeometry.DefinitePlanes

/-!
# The finite singular-line Sylow geometry

In the actual binary plus-four quadratic-isometry group, choose a singular
four-subgroup E whose normalizer meets a Sylow two-subgroup P in a Sylow
subgroup of that normalizer. The normalizer has order twelve, so the
intersection has order four. The point-line calculation identifies it with
P ∩ Ω, proves its index two and exponent two, and exhibits an element moving
either definite plane. Ω is the original Siegel-generated subgroup throughout.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the selection
immediately preceding 15.3.66 and clauses (1)--(3), printed p.1152.
-/

@[expose] public section

open Subgroup Theory.AlgebraicGroup
namespace OrthogonalFourBinary.SylowGeometry
open TerminalLines

/-- The source's Sylow selection gives order four in the line stabilizer. -/
theorem line_sylow_intersection_card (P : Sylow 2 Actor)
    (E : Subgroup (Multiplicative Space))
    (hcard : Nat.card E = 4) (hs : ∀ v ∈ E, form v.toAdd = 0)
    (Q : Sylow 2 (lineStabilizer E))
    (hQ : (Q : Subgroup (lineStabilizer E)).map (lineStabilizer E).subtype =
      (P : Subgroup Actor) ⊓ lineStabilizer E) :
    Nat.card ((P : Subgroup Actor) ⊓ lineStabilizer E : Subgroup Actor) = 4 := by
  have hc := Q.card_eq_multiplicity
  rw [singular_line_stabilizer_card E hcard hs] at hc
  have he : 2 ^ Nat.factorization 12 2 = 4 := by decide +kernel
  rw [he] at hc
  rw [← hQ, card_map_of_injective (lineStabilizer E).subtype_injective]
  exact hc

/-- The line-normalizing Sylow intersection is the genuine Ω-intersection. -/
theorem line_sylow_intersection_eq_omega (P : Sylow 2 Actor)
    (E : Subgroup (Multiplicative Space))
    (hcard : Nat.card E = 4) (hs : ∀ v ∈ E, form v.toAdd = 0)
    (Q : Sylow 2 (lineStabilizer E))
    (hQ : (Q : Subgroup (lineStabilizer E)).map (lineStabilizer E).subtype =
      (P : Subgroup Actor) ⊓ lineStabilizer E) :
    (P : Subgroup Actor) ⊓ lineStabilizer E = (P : Subgroup Actor) ⊓ omega := by
  have hc := line_sylow_intersection_card P E hcard hs Q hQ
  obtain ⟨i,rfl⟩ := singular_four_eq_graph E hcard hs
  obtain ⟨x,hx,hqx,hP⟩ := sylow_eq_point_stabilizer P
  rw [hP] at hc ⊢
  exact point_line_intersection x hx hqx i hc

/-- The source's selected line normalizer has index two in the Sylow subgroup. -/
theorem line_sylow_relIndex (P : Sylow 2 Actor)
    (E : Subgroup (Multiplicative Space))
    (hcard : Nat.card E = 4) (hs : ∀ v ∈ E, form v.toAdd = 0)
    (Q : Sylow 2 (lineStabilizer E))
    (hQ : (Q : Subgroup (lineStabilizer E)).map (lineStabilizer E).subtype =
      (P : Subgroup Actor) ⊓ lineStabilizer E) :
    ((P : Subgroup Actor) ⊓ lineStabilizer E).relIndex (P : Subgroup Actor) = 2 := by
  have hc := line_sylow_intersection_card P E hcard hs Q hQ
  have hP : Nat.card P = 8 := by
    rw [P.card_eq_multiplicity, isometryGroup_card]
    decide +kernel
  let H : Subgroup Actor := (P : Subgroup Actor) ⊓ lineStabilizer E
  have h := (H.subgroupOf (P : Subgroup Actor)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (show H ≤ P from inf_le_left)).toEquiv] at h
  change Nat.card H * H.relIndex (P : Subgroup Actor) = Nat.card P at h
  change Nat.card H = 4 at hc
  rw [hc,hP] at h
  change H.relIndex (P : Subgroup Actor) = 2
  omega

/-- The selected singular-line stabilizer in the Sylow image is a Klein four-group. -/
theorem line_sylow_isKleinFour (P : Sylow 2 Actor)
    (E : Subgroup (Multiplicative Space))
    (hcard : Nat.card E = 4) (hs : ∀ v ∈ E, form v.toAdd = 0)
    (Q : Sylow 2 (lineStabilizer E))
    (hQ : (Q : Subgroup (lineStabilizer E)).map (lineStabilizer E).subtype =
      (P : Subgroup Actor) ⊓ lineStabilizer E) :
    IsKleinFour ((P : Subgroup Actor) ⊓ lineStabilizer E : Subgroup Actor) := by
  have hc := line_sylow_intersection_card P E hcard hs Q hQ
  have he := line_sylow_intersection_eq_omega P E hcard hs Q hQ
  let H : Subgroup Actor := (P : Subgroup Actor) ⊓ lineStabilizer E
  have : Nontrivial H := Finite.one_lt_card_iff_nontrivial.mp (by rw [show Nat.card H = 4 from hc]; decide)
  refine ⟨hc, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr ?_⟩
  intro g hg
  apply orderOf_eq_prime _ hg
  apply Subtype.ext
  obtain ⟨x,hx,hqx,hP⟩ := sylow_eq_point_stabilizer P
  apply point_omega_square x hx hqx g.val
  rw [← hP, ← he]
  exact g.property

/-- Its Klein four-group differs from the stabilizer of either definite plane. -/
theorem line_sylow_ne_definite_stabilizer (P : Sylow 2 Actor)
    (E A : Subgroup (Multiplicative Space))
    (hcard : Nat.card E = 4) (hs : ∀ v ∈ E, form v.toAdd = 0)
    (hacard : Nat.card A = 4) (ha : ∀ v ∈ A, v ≠ 1 → form v.toAdd ≠ 0)
    (Q : Sylow 2 (lineStabilizer E))
    (hQ : (Q : Subgroup (lineStabilizer E)).map (lineStabilizer E).subtype =
      (P : Subgroup Actor) ⊓ lineStabilizer E) :
    (P : Subgroup Actor) ⊓ lineStabilizer E ≠ (P : Subgroup Actor) ⊓ lineStabilizer A := by
  rw [line_sylow_intersection_eq_omega P E hcard hs Q hQ]
  obtain ⟨b,rfl⟩ := definite_four_eq_plane A hacard ha
  obtain ⟨x,hx,hqx,hP⟩ := sylow_eq_point_stabilizer P
  obtain ⟨k,hk,hswap⟩ := exists_point_omega_interchange x hx hqx
  rw [hP]
  intro he
  rw [he] at hk
  exact interchange_not_mem_plane k hswap b hk.2

/-- The finite isometry-model conclusions of Aschbacher--Smith 15.3.66(1)--(3).
The Sylow condition is the source's actual choice inside the line normalizer. -/
theorem singular_line_sylow_geometry (P : Sylow 2 Actor)
    (E A : Subgroup (Multiplicative Space))
    (hcard : Nat.card E = 4) (hs : ∀ v ∈ E, form v.toAdd = 0)
    (hacard : Nat.card A = 4) (ha : ∀ v ∈ A, v ≠ 1 → form v.toAdd ≠ 0)
    (Q : Sylow 2 (lineStabilizer E))
    (hQ : (Q : Subgroup (lineStabilizer E)).map (lineStabilizer E).subtype =
      (P : Subgroup Actor) ⊓ lineStabilizer E) :
    (P : Subgroup Actor) ⊓ lineStabilizer E = (P : Subgroup Actor) ⊓ omega ∧
      ((P : Subgroup Actor) ⊓ lineStabilizer E).relIndex (P : Subgroup Actor) = 2 ∧
      IsKleinFour ((P : Subgroup Actor) ⊓ lineStabilizer E : Subgroup Actor) ∧
      (P : Subgroup Actor) ⊓ lineStabilizer E ≠ (P : Subgroup Actor) ⊓ lineStabilizer A :=
  ⟨line_sylow_intersection_eq_omega P E hcard hs Q hQ,
    line_sylow_relIndex P E hcard hs Q hQ,
    line_sylow_isKleinFour P E hcard hs Q hQ,
    line_sylow_ne_definite_stabilizer P E A hcard hs hacard ha Q hQ⟩

end OrthogonalFourBinary.SylowGeometry
