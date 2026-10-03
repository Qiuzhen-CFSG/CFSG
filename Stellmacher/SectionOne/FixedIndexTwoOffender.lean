module

public import Stellmacher.SectionsOneToFourDefs

/-!
# Fixed-index-two actors are nontrivial offenders

Under the standing Section One hypotheses, let `Y` lie in a Sylow two-subgroup
`U`. If its fixed subgroup has index two in `V` and `[V,Y]` is fixed by `Y`,
then `Y` is a nontrivial member of `oneA U`. A wrapper retains the stronger
Sylow-fixed hypothesis used by the transvection-factor consumer.

The fixedness of every first action commutator under `Y` is the
quadratic-action condition. Since `V` has exponent two, expanding
this fixedness shows that every square in `Y` acts trivially. Faithfulness
then gives exponent two for `Y`; inversion shows that `Y` is abelian.
The full fixed index rules out the trivial actor, so `|Y| ≥ 2`, and the
definition `m(Y) = |V| / (|C_V(Y)| |Y|)` gives the offender bound.

This is the generic action step used to select a factor for a fixed
transvection. Its terminology and offender definition come from the Section 1
introduction in `refs/latex/stellmacher-n-group.tex`, lines 233–258.
No graph or later-section hypotheses are used.
-/

open scoped IsMulCommutative

namespace Stellmacher.SectionOne

universe u

/-- A quadratic actor with full fixed index two is a nontrivial offender. -/
public theorem oneA_of_quadratic_fixed_index_two
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (h : Hypotheses K V) (U : Sylow 2 K) (Y : Subgroup K)
    (hYU : Y ≤ (U : Subgroup K))
    (hindex : Nat.card V = 2 * Nat.card (FixedPoints.subgroup Y V))
    (hfixed : commutatorAction Y V ≤ FixedPoints.subgroup Y V) :
    oneA (V := V) (U : Subgroup K) Y ∧ Y ≠ ⊥ := by
  have hVinv (point : V) : point⁻¹ = point := by
    apply inv_eq_of_mul_eq_one_left
    simpa [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) point
  have hYsquare (actor : Y) : actor ^ 2 = 1 := by
    apply Subtype.ext
    apply Subgroup.mem_bot.mp
    rw [← h.action_faithful, mem_fixingSubgroup_iff]
    intro point _
    have hdelta : point⁻¹ * (actor • point) ∈ commutatorAction Y V :=
      Subgroup.subset_closure ⟨actor, point, Subgroup.mem_top point, rfl⟩
    have hfix := (FixedPoints.mem_subgroup _ _ _).mp (hfixed hdelta) actor
    change (actor : K) • (point⁻¹ * ((actor : K) • point)) =
      point⁻¹ * ((actor : K) • point) at hfix
    simp only [smul_mul', hVinv] at hfix
    rw [mul_comm point] at hfix
    simpa [pow_two, mul_smul] using mul_left_cancel hfix
  have hYinv (actor : Y) : actor⁻¹ = actor := by
    apply inv_eq_of_mul_eq_one_left
    simpa [pow_two] using hYsquare actor
  have hYelementary : IsElementaryAbelian 2 Y := {
    toIsMulCommutative := ⟨⟨fun first second => by
      calc
        first * second = (first * second)⁻¹ := (hYinv _).symm
        _ = second * first := by rw [mul_inv_rev, hYinv, hYinv]⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hYsquare }
  have hYne : Y ≠ ⊥ := by
    intro hY
    have htop : FixedPoints.subgroup Y V = ⊤ := by
      subst Y
      ext point
      simp only [FixedPoints.mem_subgroup, Subgroup.mem_top, iff_true]
      intro actor
      have hactor : (actor : K) = 1 := Subgroup.mem_bot.mp actor.property
      change (actor : K) • point = point
      rw [hactor, one_smul]
    rw [htop, Subgroup.card_top] at hindex
    have hpos : 0 < Nat.card V := Nat.card_pos
    omega
  refine ⟨⟨hYU, hYelementary, ?_⟩, hYne⟩
  have hYcard : 2 ≤ Nat.card Y := (Subgroup.one_lt_card_iff_ne_bot Y).mpr hYne
  have hfixedpos : (0 : ℚ) < Nat.card (FixedPoints.subgroup Y V) :=
    Nat.cast_pos.mpr Nat.card_pos
  have hYpos : (0 : ℚ) < Nat.card Y := Nat.cast_pos.mpr Nat.card_pos
  unfold m
  apply (div_le_one (mul_pos hfixedpos hYpos)).mpr
  rw [hindex, Nat.cast_mul, Nat.cast_ofNat]
  have hYcardQ : (2 : ℚ) ≤ Nat.card Y := by exact_mod_cast hYcard
  nlinarith

/-- An index-two fixed space and a Sylow-fixed commutator recognize a
nontrivial offender without assuming elementary abelianness of the actor. -/
public theorem oneA_of_fixed_index_two
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (h : Hypotheses K V) (U : Sylow 2 K) (Y : Subgroup K)
    (hYU : Y ≤ (U : Subgroup K))
    (hindex : Nat.card V = 2 * Nat.card (FixedPoints.subgroup Y V))
    (hfixed : commutatorAction Y V ≤ FixedPoints.subgroup (U : Subgroup K) V) :
    oneA (V := V) (U : Subgroup K) Y ∧ Y ≠ ⊥ := by
  apply oneA_of_quadratic_fixed_index_two h U Y hYU hindex
  intro x hx
  rw [FixedPoints.mem_subgroup]
  intro y
  exact (FixedPoints.mem_subgroup _ _ _).mp (hfixed hx) ⟨y, hYU y.property⟩

end Stellmacher.SectionOne
