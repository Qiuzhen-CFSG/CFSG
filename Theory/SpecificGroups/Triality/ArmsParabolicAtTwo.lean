module

public import Theory.SpecificGroups.Triality.FullParabolicActions.Definitions
public import Theory.SpecificGroups.Triality.FullParabolicActions.CyclicQuotient

/-!
# The full arms parabolic of triality at q = 2

The torus has one unit coordinate in GF(q³) and one in GF(q). At q=2 the
latter coordinate is trivial; the former is the actual arms Levi torus.
Consequently the full arms Levi equals its subsystem Levi, and the full
arms parabolic equals its root-defined local factor. Its actual two-core
quotient is therefore PSL₂(8).

This identifies the full first endpoint required by Aschbacher--Smith
14.2.16--18, printed pp.986--987, using F.1.12(I)(4), pp.263--264.
The local factor uses the prime-to-two residual convention; no claim about
the two-residual or perfectness is made here.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups

namespace Triality.Standard.Parabolics
open RadicalCoordinates ConcreteBruhat ConcreteBruhat.TorusCoordinates

/-- At q=2 the full torus belongs to the arms subsystem Levi. -/
theorem torus_le_arms_levi_at_two (P : Parameters) (hp : P.prime = 2) (hq : P.q = 2) :
    torus P ≤ levi P .arms := by
  have hc : Nat.card (fixedField P)ˣ = 1 := by
    rw [Nat.card_units, card_fixedField, hq]
  let : Subsingleton (fixedField P)ˣ := (Nat.card_eq_one_iff_unique.mp hc).1
  intro t ht
  obtain ⟨⟨x,y⟩, he⟩ := (torusMulEquiv P hp).surjective ⟨t,ht⟩
  have hy : y = 1 := Subsingleton.elim _ _
  subst y
  have he' := congrArg Subtype.val he
  rw [torusMulEquiv_val] at he'
  change toCarrier P (orbitElementary P hp (x,1)) = t at he'
  rw [← he']
  have hone : foldedTorusElementary P hp .central 1 = 1 := by
    apply LeviCommutators.elementaryInclusion_injective P
    exact (inclusion_foldedTorus_central P hp 1).trans
      ((congrArg (torusWord P 1) (map_one (fixedUnit P))).trans
        ((torusWord_one P hp 1).trans (map_one (elementaryInclusion P)).symm))
  change toCarrier P (foldedTorusElementary P hp .arms x *
    foldedTorusElementary P hp .central 1) ∈ levi P .arms
  simp only [hone, mul_one]
  exact LeviCommutators.torusActor_mem_levi P hp .arms x

/-- Thus the full arms parabolic has no extra torus factor at q=2. -/
theorem fullLevi_arms_eq_levi_at_two (P : Parameters) (hp : P.prime = 2) (hq : P.q = 2) :
    fullLevi P .arms = levi P .arms := by
  rw [fullLevi_eq P hp, sup_eq_left.mpr (torus_le_arms_levi_at_two P hp hq)]

theorem parabolic_arms_eq_localFactor_at_two (P : Parameters) (hp : P.prime = 2)
    (hq : P.q = 2) : parabolic P .arms = localFactor P .arms := by
  rw [parabolic_eq_localFactor_sup_torus P hp]
  exact sup_eq_left.mpr ((torus_le_arms_levi_at_two P hp hq).trans
    (levi_le_localFactor P hp .arms))

/-- The full first endpoint, not only its root-defined local factor, has the
literal PSL₂(q³) two-core quotient at q=2. -/
def parabolicArmsQuotientEquivPSL2AtTwo (P : Parameters) (hp : P.prime = 2)
    (hq : P.q = 2) : parabolic P .arms ⧸ pCore 2 (parabolic P .arms) ≃*
      PSL(2, ExtensionField P) :=
  let f := MulEquiv.subgroupCongr (parabolic_arms_eq_localFactor_at_two P hp hq)
  (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans
    (localFactorArmsQuotientEquivPSL2 P hp)

end Triality.Standard.Parabolics
