/-
Copyright (c) 2026 Gerald Höhn. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.SplitOddCentralizers.IsometryQuotients.ShellTransport
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.SplitOddCentralizers.ResidualContainment
public import Mathlib.GroupTheory.PGroup

/-!
# The full isometry quotient by the elementary group

Elementary transport makes equal-value reflections equal modulo the actual
Siegel-generated subgroup. Their images are consequently central; reflection
generation and the reflection square identity make the whole quotient have
exponent two. For a finite space its order is a power of two, hence prime to
any odd characteristic. Since Siegel generators are killed by the field
characteristic, the elementary subgroup is exactly the prime-to-p residual.

The reflection covariance and centrality proofs adapt
`Atlas/LinearGroups/Orthogonal/ReflectionConjugation.lean` and
`ElementaryQuotient.lean`. The exponent, index and residual conclusions are
added here. We use CFSG's literal isometry carrier and normality theorem,
with public module boundaries adapted to Lean 4.33. This argument requires
two hyperbolic pairs, but no perfectness and no exclusion of the field F₃.
Source: GLS3 §2.7; Aschbacher–Smith A.2.17, printed p.39.
-/

@[expose] public noncomputable section
universe u
open Theory.AlgebraicGroup
namespace ClassicalOrthogonal.ReflectionGeneration
open ClassicalOrthogonal.Quadratic
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

theorem reflectionElement_conj (g : quadraticIsometrySubgroup Q) (a : V) (ha : Q a ≠ 0) :
    g * reflectionElement Q a ha * g⁻¹ =
      reflectionElement Q (g.val a) (by exact ne_of_eq_of_ne ((isometryCarrierEquiv Q g).map_app a) ha) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change g.val (reflectionLinear Q a ha (g.val.symm x)) = reflectionLinear Q (g.val a) (by exact ne_of_eq_of_ne ((isometryCarrierEquiv Q g).map_app a) ha) x
  rw [reflectionLinear_apply, reflectionLinear_apply, map_sub, map_smul, g.val.apply_symm_apply]
  have hq : Q (g.val a) = Q a := (isometryCarrierEquiv Q g).map_app a
  have hp := isometry_polar Q (isometryCarrierEquiv Q g) (g.val.symm x) a
  change Q.polarBilin (g.val (g.val.symm x)) (g.val a) = Q.polarBilin (g.val.symm x) a at hp
  rw [g.val.apply_symm_apply] at hp
  rw [hq, hp]

theorem reflectionElement_inv (a : V) (ha : Q a ≠ 0) :
    (reflectionElement Q a ha)⁻¹ = reflectionElement Q a ha := by
  apply Subtype.ext
  exact Module.reflection_symm (reflectionFunctional_self Q a ha)

theorem reflectionElement_square (a : V) (ha : Q a ≠ 0) :
    (reflectionElement Q a ha)^2 = 1 := by
  rw [pow_two]
  have h := inv_mul_cancel (reflectionElement Q a ha)
  rwa [reflectionElement_inv] at h

end ClassicalOrthogonal.ReflectionGeneration

namespace ClassicalOrthogonal.Fundamental.SplitOddBlocks.IsometryQuotients
open ClassicalOrthogonal.Quadratic ClassicalOrthogonal.ReflectionGeneration
attribute [local instance] elementary_normal
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V) (H : WittTwoFrame Q)
  (hQ : Q.polarBilin.Nondegenerate) (h2 : (2 : F) ≠ 0)

abbrev ElementaryQuotient := quadraticIsometrySubgroup Q ⧸ elementarySubgroup Q

def elementaryProjection : quadraticIsometrySubgroup Q →* ElementaryQuotient Q :=
  QuotientGroup.mk' (elementarySubgroup Q)

include H hQ h2 in
/-- Reflections in equal-norm vectors have the same image modulo the actual elementary subgroup. -/
theorem elementaryProjection_reflection_equal_value (a b : V) (ha : Q a ≠ 0)
    (hb : Q b ≠ 0) (hval : Q a = Q b) :
    elementaryProjection Q (reflectionElement Q a ha) =
      elementaryProjection Q (reflectionElement Q b hb) := by
  obtain ⟨g, hg, hga⟩ := elementary_transport_equal_value Q H hQ h2 a b ha hval
  have hg' : elementaryProjection Q g = 1 := by
    change (g : ElementaryQuotient Q) = 1
    exact (QuotientGroup.eq_one_iff g).mpr hg
  have he := congrArg (elementaryProjection Q) (reflectionElement_conj Q g a ha)
  rw [map_mul, map_mul, map_inv, hg', one_mul, inv_one, mul_one] at he
  simpa only [hga] using he

include H hQ h2 in
/-- Every reflection image is central in the elementary quotient. -/
theorem elementaryProjection_reflection_central (a : V) (ha : Q a ≠ 0) :
    elementaryProjection Q (reflectionElement Q a ha) ∈ Subgroup.center (ElementaryQuotient Q) := by
  rw [Subgroup.mem_center_iff]
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (elementarySubgroup Q) x
  have hga : Q (g.val a) ≠ 0 := ne_of_eq_of_ne ((isometryCarrierEquiv Q g).map_app a) ha
  have hv := elementaryProjection_reflection_equal_value Q H hQ h2 (g.val a) a hga ha
    ((isometryCarrierEquiv Q g).map_app a)
  have he := congrArg (elementaryProjection Q) (reflectionElement_conj Q g a ha)
  rw [hv, map_mul, map_mul, map_inv] at he
  have ht := congrArg (fun z => z * elementaryProjection Q g) he
  change elementaryProjection Q g * elementaryProjection Q (reflectionElement Q a ha) =
    elementaryProjection Q (reflectionElement Q a ha) * elementaryProjection Q g
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using ht

include H hQ h2 in
/-- Reflection generation and elementary shell transitivity make the quotient abelian. -/
theorem elementaryQuotient_isMulCommutative : IsMulCommutative (ElementaryQuotient Q) := by
  have hr : reflectionSubgroup Q ≤ (Subgroup.center (ElementaryQuotient Q)).comap
      (elementaryProjection Q) := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨a, ha, rfl⟩
    exact elementaryProjection_reflection_central Q H hQ h2 a ha
  rw [reflectionSubgroup_eq_top Q hQ h2] at hr
  apply isMulCommutative_iff.mpr
  intro x y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (elementarySubgroup Q) y
  exact (Subgroup.mem_center_iff.mp (hr (Subgroup.mem_top g))) x

include H hQ h2 in
/-- Every element of the actual full isometry quotient has square one. -/
theorem elementaryQuotient_square (x : ElementaryQuotient Q) : x ^ 2 = 1 := by
  have hcomm := elementaryQuotient_isMulCommutative Q H hQ h2
  have hpow (g : quadraticIsometrySubgroup Q) (hg : g ∈ reflectionSubgroup Q) :
      elementaryProjection Q g ^ 2 = 1 := by
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨a, ha, rfl⟩ := hg
      rw [← map_pow, reflectionElement_square, map_one]
    | one => simp only [map_one, one_pow]
    | mul a b _ _ ha hb =>
      have hc : Commute (elementaryProjection Q a) (elementaryProjection Q b) :=
        isMulCommutative_iff.mp hcomm _ _
      rw [map_mul, hc.mul_pow, ha, hb, one_mul]
    | inv a _ ha => rw [map_inv, inv_pow, ha, inv_one]
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (elementarySubgroup Q) x
  exact hpow g (by rw [reflectionSubgroup_eq_top Q hQ h2]; trivial)

include H hQ h2 in
/-- The full isometry quotient is a two-group, including over F₃. -/
theorem elementaryQuotient_isTwoGroup : IsPGroup 2 (ElementaryQuotient Q) := by
  apply isPGroup_iff_pow_pow_eq_one.mpr
  intro x
  exact ⟨1, by simpa only [pow_one] using elementaryQuotient_square Q H hQ h2 x⟩

include H hQ h2 in
/-- Only powers of two can divide the elementary subgroup index. -/
theorem elementary_index_dvd_two_pow [Finite V] :
    ∃ n : ℕ, (elementarySubgroup Q).index ∣ 2 ^ n := by
  have : Finite (quadraticIsometrySubgroup Q) :=
    Finite.of_injective (fun g : quadraticIsometrySubgroup Q => (g.val : V → V))
      (fun _ _ h => Subtype.ext (LinearEquiv.ext (congrFun h)))
  exact (elementaryQuotient_isTwoGroup Q H hQ h2).exists_card_dvd_pow

include H hQ h2 in
/-- Odd primes are coprime to the full isometry index. -/
theorem elementary_index_coprime [Finite V] (p : ℕ) (hp : Odd p) :
    Nat.Coprime p (elementarySubgroup Q).index := by
  obtain ⟨n, hn⟩ := elementary_index_dvd_two_pow Q H hQ h2
  exact (hp.coprime_two_right.pow_right n).coprime_dvd_right hn

omit [FiniteDimensional F V] in
/-- Once the full isometry index is prime to the characteristic, the actual
Siegel subgroup is the prime-to-p residual. This criterion also applies in rank one. -/
theorem primeToResidual_eq_elementary_of_index (p : ℕ) [CharP F p]
    (hi : Nat.Coprime p (elementarySubgroup Q).index) :
    Subgroup.primeToResidual p (quadraticIsometrySubgroup Q) = elementarySubgroup Q := by
  apply le_antisymm (Subgroup.primeToResidual_le _ hi)
  intro g hg
  exact elementary_map_mem_primeToResidual p Q (elementarySubgroup Q).subtype ⟨g, hg⟩

include H hQ h2 in
/-- The residual identification on the literal full isometry group. -/
theorem primeToResidual_eq_elementary [Finite V] (p : ℕ) [CharP F p] (hp : Odd p) :
    Subgroup.primeToResidual p (quadraticIsometrySubgroup Q) = elementarySubgroup Q :=
  primeToResidual_eq_elementary_of_index Q p (elementary_index_coprime Q H hQ h2 p hp)

end ClassicalOrthogonal.Fundamental.SplitOddBlocks.IsometryQuotients
