/-
Copyright (c) 2026 Gerald Höhn. All rights reserved.
Parts adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
The adapted portions are covered by the ATLAS Research and Attribution
License 1.0 (LICENSES/ATLAS.txt).
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.OmegaInvariants.Spinor.QuotientBound
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.OmegaInvariants.Determinant
public import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# Recognizing the full commutator from reflection values

Given a homomorphism to field square classes which takes a reflection in `a`
to the class of `Q a`, its common kernel with determinant is the full
orthogonal commutator. One hyperbolic pair gives simultaneous surjectivity
onto the two signs and two square classes; the independently proved upper
bound on the abelianization then identifies the kernel.

`ReflectionCharacter` specifies only the reflection values of a homomorphism.
Its existence is a separate mathematical obligation: this module neither
defines Omega as that kernel nor presumes the kernel comparison. The resulting
comparison is applied to the literal minus spaces in `Spinor.lean`.

The determinant and surjectivity calculations adapt ATLAS
`LinearAlgebra/QuadraticDeterminant.lean` and
`LinearGroups/Orthogonal/{SpinorKernel,IntrinsicKernelIdentification}.lean`.
The commutator argument replaces their Witt-index-two hypothesis by nonzero
value representation. Sources: GLS3 §2.7; Aschbacher–Smith A.2.17, p.39.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Theory.AlgebraicGroup
namespace ClassicalOrthogonal.SpinorInvariants
open ClassicalOrthogonal.Quadratic ClassicalOrthogonal.ReflectionGeneration
universe u
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

/-- A square-class character with the standard quadratic reflection values.
Existence must be proved independently, for example by Wall's residual form. -/
structure ReflectionCharacter where
  hom : quadraticIsometrySubgroup Q →* Atlas.SquareClass F
  reflection_value : ∀ (a : V) (ha : Q a ≠ 0),
    hom (reflectionElement Q a ha) = Atlas.squareClass F (Units.mk0 (Q a) ha)

variable [FiniteDimensional F V]

/-- The determinant of the literal full-group reflection. -/
theorem reflectionElement_det (a : V) (ha : Q a ≠ 0) :
    LinearEquiv.det (reflectionElement Q a ha).val = -1 := by
  change LinearEquiv.det (reflectionLinear Q a ha) = -1
  apply Units.ext
  rw [LinearEquiv.coe_det]
  have he : (reflectionLinear Q a ha).toLinearMap =
      LinearMap.transvection (-(reflectionFunctional Q a)) a := by
    apply LinearMap.ext
    intro x
    simp only [LinearEquiv.coe_coe, reflectionLinear_apply, LinearMap.transvection.apply,
      LinearMap.neg_apply, reflectionFunctional, LinearMap.smul_apply, LinearMap.flip_apply,
      smul_eq_mul, sub_eq_add_neg, neg_smul]
  rw [he, LinearMap.transvection.det, LinearMap.neg_apply, reflectionFunctional_self Q a ha]
  change (1 : F) + -2 = -1
  ring

/-- The ordinary determinant, with its actual full orthogonal domain. -/
def orthogonalDeterminant : quadraticIsometrySubgroup Q →* Fˣ :=
  LinearEquiv.det.comp (quadraticIsometrySubgroup Q).subtype

theorem orthogonalDeterminant_square (hQ : Q.polarBilin.Nondegenerate) (h2 : (2 : F) ≠ 0)
    (g : quadraticIsometrySubgroup Q) : orthogonalDeterminant Q g ^ 2 = 1 := by
  have hg : g ∈ reflectionSubgroup Q := by rw [reflectionSubgroup_eq_top Q hQ h2]; trivial
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨a, ha, rfl⟩ := hg
    change LinearEquiv.det (reflectionElement Q a ha).val ^ 2 = 1
    rw [reflectionElement_det, neg_one_sq]
  | one => rw [map_one, one_pow]
  | mul a b _ _ ha hb => rw [map_mul, mul_pow, ha, hb, one_mul]
  | inv a _ ha => rw [map_inv, inv_pow, ha, inv_one]

/-- Determinant restricted to its two possible signs. -/
def determinantSign (hQ : Q.polarBilin.Nondegenerate) (h2 : (2 : F) ≠ 0) :
    quadraticIsometrySubgroup Q →* rootsOfUnity 2 F :=
  (orthogonalDeterminant Q).codRestrict _ (fun g =>
    (mem_rootsOfUnity 2 _).mpr (orthogonalDeterminant_square Q hQ h2 g))

/-- The two independent characters used to recognize the commutator. -/
def determinantCharacter (hQ : Q.polarBilin.Nondegenerate) (h2 : (2 : F) ≠ 0)
    (χ : ReflectionCharacter Q) :
    quadraticIsometrySubgroup Q →* rootsOfUnity 2 F × Atlas.SquareClass F :=
  (determinantSign Q hQ h2).prod χ.hom

/-- Reflection generation makes the prescribed character unique. -/
theorem reflectionCharacter_unique (hQ : Q.polarBilin.Nondegenerate) (h2 : (2 : F) ≠ 0)
    (χ ψ : ReflectionCharacter Q) : χ.hom = ψ.hom := by
  apply MonoidHom.eq_of_eqOn_dense (reflectionSubgroup_eq_top Q hQ h2)
  rintro g ⟨a, ha, rfl⟩
  rw [χ.reflection_value, ψ.reflection_value]

/-- Every sign and square class is realized, using only representation of nonzero field values. -/
theorem determinantCharacter_surjective (hQ : Q.polarBilin.Nondegenerate) (h2 : (2 : F) ≠ 0)
    (χ : ReflectionCharacter Q) (hrep : ∀ c : F, c ≠ 0 → ∃ a : V, Q a = c) :
    Function.Surjective (determinantCharacter Q hQ h2 χ) := by
  rintro ⟨c, s⟩
  obtain ⟨t, rfl⟩ := Atlas.squareClass_surjective F s
  obtain ⟨a, ha⟩ := hrep t.val t.ne_zero
  obtain ⟨b, hb⟩ := hrep 1 one_ne_zero
  have ha' : Q a ≠ 0 := ha ▸ t.ne_zero
  have hb' : Q b ≠ 0 := hb ▸ one_ne_zero
  have hea : Units.mk0 (Q a) ha' = t := Units.ext ha
  have heb : Units.mk0 (Q b) hb' = 1 := Units.ext hb
  have hc : c.val.val ^ 2 = (1 : F) :=
    congrArg Units.val ((mem_rootsOfUnity 2 c.val).mp c.prop)
  rcases sq_eq_one_iff.mp hc with hc | hc
  · refine ⟨reflectionElement Q a ha' * reflectionElement Q b hb', Prod.ext ?_ ?_⟩
    · apply Subtype.ext
      change LinearEquiv.det (reflectionElement Q a ha' * reflectionElement Q b hb').val = c.val
      rw [Subgroup.coe_mul, map_mul, reflectionElement_det, reflectionElement_det,
        neg_mul_neg, one_mul]
      exact Units.ext hc.symm
    · change χ.hom (reflectionElement Q a ha' * reflectionElement Q b hb') = _
      rw [map_mul, χ.reflection_value, χ.reflection_value, hea, heb, map_one]
      exact mul_one (Atlas.squareClass F t)
  · refine ⟨reflectionElement Q a ha', Prod.ext ?_ ?_⟩
    · apply Subtype.ext
      change LinearEquiv.det (reflectionElement Q a ha').val = c.val
      rw [reflectionElement_det]
      exact Units.ext hc.symm
    · exact (χ.reflection_value a ha').trans (congrArg (Atlas.squareClass F) hea)

theorem determinantCharacter_kernel_index [Finite F]
    (hQ : Q.polarBilin.Nondegenerate) (h2 : (2 : F) ≠ 0)
    (χ : ReflectionCharacter Q) (hrep : ∀ c : F, c ≠ 0 → ∃ a : V, Q a = c) :
    (determinantCharacter Q hQ h2 χ).ker.index = 4 := by
  have he := Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
    (determinantCharacter Q hQ h2 χ) (determinantCharacter_surjective Q hQ h2 χ hrep)).toEquiv
  change Nat.card (_ ⧸ (determinantCharacter Q hQ h2 χ).ker) = 4
  rw [he, Nat.card_prod, Atlas.card_squareOneUnits, Atlas.card_squareClass, if_neg h2]

/-- A reflection-value character and determinant cut out the literal commutator,
including spaces of Witt index one. -/
theorem commutator_eq_determinantCharacter_kernel [Finite F]
    (hQ : Q.polarBilin.Nondegenerate) (h2 : (2 : F) ≠ 0)
    (χ : ReflectionCharacter Q) (hrep : ∀ c : F, c ≠ 0 → ∃ a : V, Q a = c) :
    commutator (quadraticIsometrySubgroup Q) = (determinantCharacter Q hQ h2 χ).ker := by
  let : Finite V := Finite.of_equiv (Fin (Module.finrank F V) → F)
    (Module.finBasis F V).equivFun.symm.toEquiv
  let : Finite (quadraticIsometrySubgroup Q) := Finite.of_injective
    (fun g : quadraticIsometrySubgroup Q => (g.val : V → V))
    (fun x y h => Subtype.ext (DFunLike.coe_injective h))
  have hle : commutator (quadraticIsometrySubgroup Q) ≤
      (determinantCharacter Q hQ h2 χ).ker :=
    Abelianization.commutator_subset_ker
      (G := quadraticIsometrySubgroup Q) (A := rootsOfUnity 2 F × Atlas.SquareClass F)
      (determinantCharacter Q hQ h2 χ)
  have hupper := card_abelianization_le_four Q hQ h2 hrep
  have hindex := determinantCharacter_kernel_index Q hQ h2 χ hrep
  by_contra hne
  have hlt := Subgroup.index_strictAnti (lt_of_le_of_ne hle hne)
  rw [hindex] at hlt
  change (commutator (quadraticIsometrySubgroup Q)).index ≤ 4 at hupper
  omega

/-- Membership form of the intrinsic comparison, conditional only on construction
of the reflection-value homomorphism. -/
theorem mem_commutator_iff_det_character [Finite F]
    (hQ : Q.polarBilin.Nondegenerate) (h2 : (2 : F) ≠ 0)
    (χ : ReflectionCharacter Q) (hrep : ∀ c : F, c ≠ 0 → ∃ a : V, Q a = c)
    (g : quadraticIsometrySubgroup Q) :
    g ∈ commutator (quadraticIsometrySubgroup Q) ↔
      LinearEquiv.det g.val = 1 ∧ χ.hom g = 1 := by
  rw [commutator_eq_determinantCharacter_kernel Q hQ h2 χ hrep, MonoidHom.mem_ker]
  change (determinantSign Q hQ h2 g, χ.hom g) = (1, 1) ↔ _
  rw [Prod.mk.injEq]
  have he : determinantSign Q hQ h2 g = 1 ↔ LinearEquiv.det g.val = 1 := by
    constructor
    · exact fun h => congrArg Subtype.val h
    · exact fun h => Subtype.ext h
  rw [he]

end ClassicalOrthogonal.SpinorInvariants
