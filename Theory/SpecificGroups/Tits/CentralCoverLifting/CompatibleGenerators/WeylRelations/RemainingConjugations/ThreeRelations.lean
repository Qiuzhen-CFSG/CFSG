module
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.RemainingConjugations.DefectBounds
import Mathlib.Tactic.Group
/-!
# Three remaining normalized Weyl conjugations

The checked central-word calculation gives VII(s₄), VIII(s₂), and
VII(s₃)'s error times the square of VII(r₃)'s error equal to one.
The last equality also gives the exact VIII(r₃) equation. Thus r₃ is
conjugate to the involution r₅. Since s₇r₇ is conjugate to s₁, the central
VII(r₃) error has square one, which kills VII(s₃)'s error as well.

The final assembly below leaves only VII(r₃)'s vanishing explicit.
Its square-one bound is not a proof of that vanishing.

Source: Parrott (1972), §5, p.683, with a⁻¹*b⁻¹*a*b as commutator.
All equations hold in the literal `NormalizedPresentation` under precisely
the power/root hypothesis; no splitting or exact braid identity is assumed.
-/
public section

namespace Tits.CentralCoverLifting.CompatibleGenerators
open RemainingConjugations
open scoped commutatorElement
set_option backward.isDefEq.respectTransparency false

private theorem sqinv {G : Type*} [Group G] {a : G} (h : a ^ 2 = 1) : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using h)

variable (hroot : ∀ j, isPowerRootRelator j = true →
  FreeGroup.lift normalizedGenerator (parrottRelator j) = 1)
include hroot

/-- The two linear-word eliminations give the exact VII(s₄) equation. -/
theorem weyl_vii_s4_relation :
    FreeGroup.lift normalizedGenerator (parrottRelator .vii_s4) = 1 :=
  (remaining_defect_bounds hroot).1

/-- The two linear-word eliminations give the exact VIII(s₂) equation. -/
theorem weyl_viii_s2_relation :
    FreeGroup.lift normalizedGenerator (parrottRelator .viii_s2) = 1 :=
  (remaining_defect_bounds hroot).2.1

/-- VIII(r₃) is exact: its central error is the product eliminated by the
checked word calculation. -/
theorem weyl_viii_r3_relation :
    FreeGroup.lift normalizedGenerator (parrottRelator .viii_r3) = 1 := by
  have hh := normalized_relator_value hroot .viii_r3
  have hx := (remaining_defect_bounds hroot).2.2.1
  simpa [sourceCoeff, Context.scalar, normalizedContext, relatorValue, hx] using hh

/-- The remaining VII(r₃) error has square one. Indeed r₃ is conjugate to
r₅, and s₇r₇ is conjugate to s₁; all three are involutions. -/
theorem weyl_vii_r3_defect_square :
    (FreeGroup.lift normalizedGenerator (parrottRelator .vii_r3)) ^ 2 = 1 := by
  let a := normalizedGenerator .r1
  let b := normalizedGenerator .r8
  let c := normalizedGenerator .s1
  let g := normalizedGenerator .s5
  let r := FreeGroup.lift normalizedGenerator parrottR3
  let s := c * g ^ 2
  let u := normalizedGenerator .s7 * FreeGroup.lift normalizedGenerator parrottR7
  let z := FreeGroup.lift normalizedGenerator (parrottRelator .vii_r3)
  have ha : a ^ 2 = 1 := by
    simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of] using hroot .i_r1 rfl
  have hb : b ^ 2 = 1 := by
    simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of] using hroot .i_r8 rfl
  have hc : c ^ 2 = 1 := by
    simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of] using hroot .i_s1 rfl
  have hg : g ^ 4 = 1 := by
    simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of] using hroot .i_s5 rfl
  have hcg : Commute c g := by
    have hh : ⁅c⁻¹, g⁻¹⁆ = 1 := by
      simpa only [parrottRelator, parrottCommutator, map_mul, map_inv,
        FreeGroup.lift_apply_of, commutatorElement_def, inv_inv] using hroot .ii_s1_s5 rfl
    simpa only [inv_inv] using (commutatorElement_eq_one_iff_commute.mp hh).inv_inv
  have hs : s ^ 2 = 1 := by
    rw [(hcg.pow_right 2).mul_pow, hc, one_mul, ← pow_mul]
    exact hg
  have hz : z ∈ Subgroup.center NormalizedPresentation := normalizedGenerator_relators_central _
  have hbr : MulAut.conj b r = s := by
    have hh : b * r * b * s⁻¹ = 1 := by
      simpa only [parrottRelator, parrottR5, map_mul, map_inv, map_pow,
        FreeGroup.lift_apply_of] using weyl_viii_r3_relation hroot
    simpa only [MulAut.conj_apply, sqinv hb] using mul_inv_eq_one.mp hh
  have hbu : MulAut.conj b c = u := by
    have hh : b * c * b * u⁻¹ = 1 := by
      have hh := normalized_relator_value hroot .viii_s1
      have hh' : FreeGroup.lift normalizedGenerator (parrottRelator .viii_s1) = 1 := by
        simpa [sourceCoeff, Context.scalar] using hh
      simpa only [parrottRelator, map_mul, map_inv, FreeGroup.lift_apply_of] using hh'
    simpa only [MulAut.conj_apply, sqinv hb] using mul_inv_eq_one.mp hh
  have hr : r ^ 2 = 1 := by
    apply (MulAut.conj b).injective
    rw [map_pow, map_one, hbr, hs]
  have hu : u ^ 2 = 1 := by rw [← hbu, ← map_pow, hc, map_one]
  have har : MulAut.conj a r = u * z := by
    have hv : a * r * a * u⁻¹ = z := by
      simp only [z, parrottRelator, map_mul, map_inv, FreeGroup.lift_apply_of]
      rfl
    simpa only [MulAut.conj_apply, sqinv ha] using
      (mul_inv_eq_iff_eq_mul.mp hv).trans (hz.comm _).eq
  have hh := congrArg (MulAut.conj a) hr
  rw [map_pow, map_one, har, (hz.comm u).symm.mul_pow, hu, one_mul] at hh
  exact hh

/-- The VII(s₃) error is inverse to the square of the VII(r₃) error;
the latter square has just been shown to be one. -/
theorem weyl_vii_s3_relation :
    FreeGroup.lift normalizedGenerator (parrottRelator .vii_s3) = 1 := by
  simpa only [weyl_vii_r3_defect_square hroot, mul_one] using
    (remaining_defect_bounds hroot).2.2.1

/-- Three of the four remaining equations are proved. This assembly isolates
the only unresolved premise, the vanishing of the central VII(r₃) involution. -/
theorem weyl_remaining_conjugation_relations_of_vii_r3
    (hr3 : FreeGroup.lift normalizedGenerator (parrottRelator .vii_r3) = 1) :
    ∀ j, isRemainingWeylConjugation j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1 := by
  intro j hj
  cases j <;> first
    | exact weyl_vii_s4_relation hroot
    | exact weyl_viii_s2_relation hroot
    | exact weyl_vii_s3_relation hroot
    | exact hr3
    | cases hj
end Tits.CentralCoverLifting.CompatibleGenerators
