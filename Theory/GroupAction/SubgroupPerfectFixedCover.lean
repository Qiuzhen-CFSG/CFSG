module
public import Theory.GroupAction.PerfectFixedCover
public import Theory.GroupAction.SubgroupConjugation

/-!
# Perfect supplements in ambient centralizers

Let A normalize a finite subgroup K and act trivially on K/N, where N is
characteristic, solvable, and of order coprime to A. Coprime fixed-point
lifting makes the literal map C_K(A) -> K/N surjective. If K is perfect,
the solvable residual of C_K(A) still maps onto K/N, and its ambient image
times N is exactly K.

This translates the fixed-point theorem to original ambient inclusions,
without replacing the solvable residual by a prime residual or assuming
that K is normal in the ambient group.
Source: the coprime fixed-cover argument of Aschbacher--Smith 4.4.5, p.620;
application to the remaining 11.5.6(3) component row, pp.780--781.
-/

public section
open Subgroup
open scoped commutatorElement Pointwise

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The actual centralizer covers the quotient by a solvable coprime characteristic kernel. -/
theorem centralizer_quotient_surjective_of_solvable_coprime
    (K A : Subgroup G) (N : Subgroup K) [N.Characteristic]
    (hn : A ≤ normalizer (K : Set G))
    (hs : Group.IsSolvable N) (hc : Nat.Coprime (Nat.card A) (Nat.card N))
    (hm : ⁅K,A⁆ ≤ N.map K.subtype) :
    Function.Surjective ((QuotientGroup.mk' N).comp
      (inclusion (show K ⊓ centralizer (A : Set G) ≤ K from inf_le_left))) := by
  let : MulDistribMulAction A K := conjMulDistribMulActionOfLeNormalizer A K hn
  let : IsInvariant A K N := isInvariant_of_characteristic N
  have hdis (a : A) (k : K) : k⁻¹ * (a • k) ∈ N := by
    have hh := commutator_le.mp (show ⁅A,K⁆ ≤ N.map K.subtype by
      rw [commutator_comm]; exact hm) a a.property k k.property
    obtain ⟨v,hv,he⟩ := hh
    have hv' : (a • k) * k⁻¹ ∈ N := by
      have he' : v = (a • k) * k⁻¹ := Subtype.ext he
      exact he' ▸ hv
    have heq : QuotientGroup.mk' N (a • k) = QuotientGroup.mk' N k := by
      have h := (QuotientGroup.eq_one_iff (N := N) _).mpr hv'
      change QuotientGroup.mk' N ((a • k) * k⁻¹) = 1 at h
      rw [map_mul,map_inv,mul_inv_eq_one] at h
      exact h
    exact QuotientGroup.eq.mp heq.symm
  have hsurj := Theory.GroupAction.fixedPoint_quotient_surjective_of_solvable_coprime_displacement
    N hs hc hdis
  intro y
  obtain ⟨k,hk⟩ := hsurj y
  refine ⟨⟨k,k.val.property,?_⟩,hk⟩
  apply mem_centralizer_iff.mpr
  intro a ha
  have h := congrArg Subtype.val (k.property (⟨a,ha⟩ : A))
  change a * (k.val : G) * a⁻¹ = k.val at h
  exact mul_inv_eq_iff_eq_mul.mp h

/-- The original quotient restricted to the perfect residual of the centralizer is onto. -/
theorem residual_centralizer_quotient_surjective_of_solvable_coprime
    (K A : Subgroup G) [Group.IsPerfect K] (N : Subgroup K) [N.Characteristic]
    (hn : A ≤ normalizer (K : Set G))
    (hs : Group.IsSolvable N) (hc : Nat.Coprime (Nat.card A) (Nat.card N))
    (hm : ⁅K,A⁆ ≤ N.map K.subtype) :
    Function.Surjective (((QuotientGroup.mk' N).comp
      (inclusion (show K ⊓ centralizer (A : Set G) ≤ K from inf_le_left))).comp
        (solvableResidual (K ⊓ centralizer (A : Set G) : Subgroup G)).subtype) := by
  let f := (QuotientGroup.mk' N).comp
    (inclusion (show K ⊓ centralizer (A : Set G) ≤ K from inf_le_left))
  let : Group.IsPerfect (K ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  have he : (solvableResidual (K ⊓ centralizer (A : Set G) : Subgroup G)).map f = ⊤ := by
    rw [map_solvableResidual_eq f
      (centralizer_quotient_surjective_of_solvable_coprime K A N hn hs hc hm),
      solvableResidual_eq_top]
  intro y
  obtain ⟨k,hk,hky⟩ := he.symm ▸ (mem_top y)
  exact ⟨⟨k,hk⟩,hky⟩
end Subgroup

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Coprime fixed points supply a perfect supplement to the solvable kernel. -/
theorem residual_centralizer_mul_kernel_eq
    (K A : Subgroup G) [Group.IsPerfect K] (N : Subgroup K) [N.Characteristic]
    (hn : A ≤ normalizer (K : Set G))
    (hs : Group.IsSolvable N) (hc : Nat.Coprime (Nat.card A) (Nat.card N))
    (hm : ⁅K,A⁆ ≤ N.map K.subtype) :
    (((solvableResidual (K ⊓ centralizer (A : Set G) : Subgroup G)).map
        (K ⊓ centralizer (A : Set G)).subtype : Subgroup G) : Set G) *
      (N.map K.subtype : Set G) = (K : Set G) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨j,⟨j,hj,rfl⟩,n,⟨n,hn,rfl⟩,rfl⟩
    exact K.mul_mem j.property.1 n.property
  · intro k hk
    have hs := residual_centralizer_quotient_surjective_of_solvable_coprime K A N hn hs hc hm
    obtain ⟨j,hj⟩ := hs (QuotientGroup.mk' N ⟨k,hk⟩)
    let jK : K := ⟨j.val,j.val.property.1⟩
    let n : K := jK⁻¹ * ⟨k,hk⟩
    have hn : n ∈ N := QuotientGroup.eq.mp hj
    refine ⟨j,⟨j.val,j.property,rfl⟩,n,⟨n,hn,rfl⟩,?_⟩
    change (j.val : G) * ((j.val : G)⁻¹ * k) = k
    group
end Subgroup

