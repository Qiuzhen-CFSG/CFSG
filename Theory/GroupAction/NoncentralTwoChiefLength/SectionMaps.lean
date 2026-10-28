module

public import Theory.GroupAction.NoncentralTwoChiefLength.Native
import Mathlib.Tactic

/-!
# Cubic length through actual section maps

A surjective equivariant homomorphism with kernel `N` identifies its target
with the actual relative quotient `R/N`. We construct the quotient equivalence,
prove relative normality and invariance of its kernel, and transport the cubic
fixed-point index. Coprime fixed-point lifting then identifies the result with
the difference of the two subgroup invariants.

This packages reusable transport for the two filtration arguments in
Aschbacher–Smith 13.8.33, printed pp.967–968. No numerical contribution or
ambient normality is part of the section-map data.
-/

@[expose] public section

open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]
variable {B Y : Type*} [Group B] [Group Y] [MulDistribMulAction B Y]

/-- An actual surjective map on a subgroup, with its precise kernel and conjugation formula. -/
structure ConjugationSection (A N R : Subgroup G) (f : A →* B) where
  le : N ≤ R
  normalizes : A ≤ normalizer (R : Set G)
  projection : R →* Y
  onto : Function.Surjective projection
  kernel : projection.ker = N.subgroupOf R
  equivariant : letI := conjMulDistribMulActionOfLeNormalizer A R normalizes
    ∀ (a : A) (r : R), projection (a • r) = f a • projection r

namespace ConjugationSection
variable {A N R : Subgroup G} {f : A →* B}
variable (s : ConjugationSection (Y := Y) A N R f)
include s

theorem normal : (N.subgroupOf R).Normal := by
  rw [← s.kernel]
  infer_instance

theorem normalizes_kernel : A ≤ normalizer (N : Set G) := by
  let := conjMulDistribMulActionOfLeNormalizer A R s.normalizes
  apply le_normalizer_iff.mpr
  intro a ha n hn
  have hz : s.projection ⟨n, s.le hn⟩ = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [s.kernel]
    exact hn
  have hm : a * n * a⁻¹ ∈ R :=
    (mem_normalizer_iff.mp (s.normalizes ha) n).mp (s.le hn)
  have he : s.projection ⟨a * n * a⁻¹, hm⟩ = 1 := by
    change s.projection ((⟨a, ha⟩ : A) • (⟨n, s.le hn⟩ : R)) = 1
    rw [s.equivariant, hz, smul_one]
  have hk := MonoidHom.mem_ker.mpr he
  rw [s.kernel] at hk
  exact hk

noncomputable def quotientEquiv :
    letI := s.normal
    (R ⧸ N.subgroupOf R) ≃* Y := by
  let := s.normal
  exact (QuotientGroup.quotientMulEquivOfEq s.kernel.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective s.projection s.onto)

@[simp] theorem quotientEquiv_mk (r : R) :
    letI := s.normal
    s.quotientEquiv (QuotientGroup.mk' (N.subgroupOf R) r) = s.projection r := rfl

theorem quotientEquiv_equivariant :
    letI := s.normal
    letI := quotientConjugationAction A R N s.normalizes s.normalizes_kernel
    ∀ (a : A) q, s.quotientEquiv (a • q) = f a • s.quotientEquiv q := by
  let := s.normal
  let := quotientConjugationAction A R N s.normalizes s.normalizes_kernel
  intro a q
  obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf R) q
  exact s.equivariant a r

theorem length_eq [Finite G] (hA : IsPGroup 3 A) (hR : IsPGroup 2 R)
    (hf : Function.Surjective f) :
    sectionCubicLength A N R = FixedPoints.cubicLength B Y := by
  let := s.normal
  let := quotientConjugationAction A R N s.normalizes s.normalizes_kernel
  rw [sectionCubicLength_eq_quotient_of_twoGroup A R N hA hR s.le
    s.normalizes s.normalizes_kernel]
  exact FixedPoints.cubicLength_eq_of_equivariant_surjective_actor f hf
    s.quotientEquiv s.quotientEquiv_equivariant
end ConjugationSection
end Subgroup
