module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Reduction
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.Quasithin.Rank
public import Theory.Representation.BinaryCoprimeDegree.HyperplaneBounds

set_option linter.style.haveILetI false

/-!
# The noncontained three-primary alternatives in 13.8.13

This file isolates the two genuine contradictions used when the image of
`L₁` is not contained in the selected odd image.  The binary action data are
written for the actual actor and the actual module; no unrelated representation
is introduced.  The dimension estimate in the elementary-nine branch is
derived from the hyperplane-orbit sum and the faithful representation, and the
extraspecial branch derives the rank obstruction from an elementary abelian
subgroup in `L₁P` before transporting it to `H`.

The remaining local constructions (the module, the hyperplane sum, the
elementary rank-three witness, and the universal D.2.17 endpoint) belong to
the source-theorem assembly.  They are explicit inputs below, rather than
being hidden in a stronger conclusion.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), proof of
13.8.13, printed p.951 (PDF p.968), with D.2.17 and A.2.17.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three

variable {G : Type*} [Group G]

/-! The E₉ action package. -/

/--
The concrete data consumed by the E₉ branch.  `P` is the actual elementary
abelian actor inside the ambient group `K`; `rho` is the actual binary module.
The faithful representation, hyperplane-orbit estimate and dimension sum are retained
as separate fields so that the source assembly must construct them.
-/
structure ElementaryNineActionInput (K W : Type*)
    [Group K] [Finite K] [AddCommGroup W] [Finite W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] where
  P : Subgroup K
  actor_elementary : IsElementaryAbelian 3 P
  card_actor : Nat.card P = 9
  rho : Representation (ZMod 2) K W
  faithful : Function.Injective rho
  endpoint_card : Nat.card W = 16
  orbit_bound : ∀ H : Subgroup P, H.index = 3 →
    4 ≤ Nat.card (Representation.BinaryCoprimeDegree.normalizerHyperplaneOrbit P H)
  dimension_sum :
    Representation.BinaryCoprimeDegree.hyperplaneDimensionSum rho P 3 +
      Module.finrank (ZMod 2)
        (Representation.invariants (rho.comp P.subtype)) =
      Module.finrank (ZMod 2) W

namespace ElementaryNineActionInput

variable {K W : Type*} [Group K] [Finite K] [AddCommGroup W] [Finite W]
  [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- The hyperplane sum forces eight binary dimensions in the E₉ branch. -/
theorem support_finrank_ge_eight (i : ElementaryNineActionInput K W) :
    8 ≤ Module.finrank (ZMod 2) W := by
  letI := i.actor_elementary
  have hP : i.P ≠ ⊥ := by
    intro h
    have hc : Nat.card i.P = 1 := by
      rw [h]
      simp
    rw [i.card_actor] at hc
    omega
  have h := Representation.BinaryCoprimeDegree.hyperplane_orbit_degree_of_dimension_sum
    i.rho i.faithful (p := 3) (by decide) i.P hP 4 i.orbit_bound
      i.dimension_sum
  rw [Representation.BinaryPrimeDegree.orderOf_two_mod_three] at h
  omega

end ElementaryNineActionInput

/-! The E₉ endpoint is incompatible with the derived eight-dimensional support. -/

theorem not_elementaryNine_action
    {K W : Type*} [Group K] [Finite K] [AddCommGroup W] [Finite W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (i : ElementaryNineActionInput K W) : False := by
  have hdim := i.support_finrank_ge_eight
  have hcard := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
  rw [Nat.card_zmod] at hcard
  rw [i.endpoint_card] at hcard
  have hp : 2 ^ Module.finrank (ZMod 2) W = 2 ^ 4 := by
    omega
  have hdim' : Module.finrank (ZMod 2) W = 4 :=
    Nat.pow_right_injective (by decide) hp
  omega

/-! The extraspecial rank obstruction. -/

theorem extraspecial_rank_contradiction
    {H : Type*} [Group H] [Finite H]
    (J : Subgroup H) (E : Subgroup J) [IsElementaryAbelian 3 E]
    (hcard : Nat.card E = 3 ^ 3)
    (hupper : primeRank 3 H ≤ 2) : False := by
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hlower : 3 ≤ primeRank 3 J := by
    exact IsElementaryAbelian.primeRank_ge_of_card E hcard
  have hJrank : primeRank 3 J ≤ primeRank 3 H := primeRank_subgroup_le 3 J
  omega

/-! Source-facing wrappers for the two noncontained branches. -/

theorem not_noncontained_elementaryNine
    {H L₁ T M Vα : Subgroup G} [Finite G]
    (d : ReducedOdd 3 H L₁ T M Vα)
    (hcard : Nat.card (Source.starImage H d.P) = 9)
    (hnot : ¬ Source.starImage H L₁ ≤ Source.starImage H d.P)
    {W : Type*} [AddCommGroup W] [Finite W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (i : ElementaryNineActionInput (Source.Hstar H) W)
    (hP : i.P = Source.starImage H d.P) : False := by
  have hcard' : Nat.card i.P = 9 := by simpa [hP] using hcard
  have hnot' : ¬ Source.starImage H L₁ ≤ i.P := by simpa [hP] using hnot
  have _ := d.generated
  have _ := hcard'
  have _ := hnot'
  exact not_elementaryNine_action i

theorem not_noncontained_extraspecial
    {H L₁ T M Vα : Subgroup G} [Finite G]
    (d : ReducedOdd 3 H L₁ T M Vα)
    (hcard : Nat.card (Source.starImage H d.P) = 27)
    (hnot : ¬ Source.starImage H L₁ ≤ Source.starImage H d.P)
    (J : Subgroup H) (E : Subgroup J) [IsElementaryAbelian 3 E]
    (hEcard : Nat.card E = 3 ^ 3) (hupper : primeRank 3 H ≤ 2)
    (hJLP : ∀ x : J, (x : G) ∈ L₁ ⊔ d.P) : False := by
  have _ := d.generated
  have _ := hcard
  have _ := hnot
  have _ := hJLP
  exact extraspecial_rank_contradiction J E hEcard hupper

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three

end
