module

public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupTheory.CyclicTwoAut
import Mathlib.Tactic.Group

/-!
# Automorphisms detected by a subgroup with cyclic centralizer

If a characteristic subgroup has a p-group centralizer whose automorphism
group is also a p-group, its restriction kernel is a p-group. An automorphism
fixing the subgroup displaces every element into its centralizer, so belongs
to the kernel of the quotient action by that characteristic centralizer.

In particular a cyclic centralizer in a finite two-group suffices. This is
the automorphism-detection step for the large Hall central products in
Janko–Thompson, Math. Z. 113 (1970), §4, p.392.
-/

namespace Subgroup

private theorem displacement_mem_centralizer {G : Type*} [Group G]
    (N : Subgroup G) [N.Characteristic]
    (f : (MulAut.characteristic N).ker) (x : G) :
    x⁻¹ * (f : MulAut G) x ∈ centralizer (N : Set G) := by
  have hfix (n : G) (hn : n ∈ N) : (f : MulAut G) n = n :=
    congrArg Subtype.val (DFunLike.congr_fun f.property (⟨n, hn⟩ : N))
  intro n hn
  have h := hfix (x * n * x⁻¹) ((inferInstance : N.Normal).conj_mem n hn x)
  simp only [map_mul, map_inv, hfix n hn] at h
  have hh := congrArg (fun t : G => x⁻¹ * t * (f : MulAut G) x) h
  group at hh
  simpa only [mul_assoc, zpow_neg_one] using hh.symm

/-- A characteristic subgroup detects automorphisms up to a p-group kernel
when its centralizer and the centralizer's automorphism group are p-groups. -/
public theorem isPGroup_characteristic_restriction_kernel_of_centralizer_mulAut
    {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Characteristic] {p : ℕ}
    (hC : IsPGroup p (centralizer (N : Set G)))
    (hAut : IsPGroup p (MulAut (centralizer (N : Set G)))) :
    IsPGroup p (MulAut.characteristic N).ker := by
  let C := centralizer (N : Set G)
  have hle : (MulAut.characteristic N).ker ≤ (quotientAut C).ker := by
    intro f hf
    change quotientAut C f = 1
    apply MulEquiv.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H x =>
      change quotientAut C f (QuotientGroup.mk' C x) = QuotientGroup.mk' C x
      rw [quotientAut_apply_mk]
      exact (QuotientGroup.eq.mpr (displacement_mem_centralizer N ⟨f, hf⟩ x)).symm
  exact (isPGroup_quotientAut_kernel_of_mulAut C hC hAut).to_le hle

/-- A characteristic subgroup with cyclic centralizer in a finite two-group
has a two-group restriction kernel. -/
public theorem isPGroup_characteristic_restriction_kernel_of_cyclic_centralizer
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (N : Subgroup P) [N.Characteristic]
    [IsCyclic (centralizer (N : Set P))] :
    IsPGroup 2 (MulAut.characteristic N).ker :=
  isPGroup_characteristic_restriction_kernel_of_centralizer_mulAut N
    (hP.to_subgroup _) (hP.to_subgroup _).mulAut_of_isCyclic_two

end Subgroup
