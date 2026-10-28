module

public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
import Mathlib.Tactic.Group

/-!
# Restriction to a self-centralizing characteristic subgroup

If a characteristic p-subgroup contains its centralizer, the kernel of
restriction of ambient automorphisms to that subgroup is a p-group.
Indeed, an automorphism fixing the subgroup pointwise displaces every
ambient element by an element of its centralizer. It therefore fixes both
the subgroup and the quotient, reducing to the paired automorphism kernel.

This is the elementary automorphism-detection step for Thompson critical
subgroups; see Gorenstein, *Finite Groups*, Theorem 5.3.11, pp.185–186.
It uses only the characteristic and centralizer conditions.
-/

namespace Subgroup

private theorem displacement_mem {G : Type*} [Group G]
    (C : Subgroup G) [C.Characteristic]
    (hself : centralizer (C : Set G) ≤ C)
    (f : (MulAut.characteristic C).ker) (x : G) :
    x⁻¹ * (f : MulAut G) x ∈ C := by
  have hfix (c : G) (hc : c ∈ C) : (f : MulAut G) c = c :=
    congrArg Subtype.val (DFunLike.congr_fun f.property (⟨c, hc⟩ : C))
  apply hself
  intro c hc
  have h := hfix (x * c * x⁻¹) ((inferInstance : C.Normal).conj_mem c hc x)
  simp only [map_mul, map_inv, hfix c hc] at h
  have hh := congrArg (fun t : G => x⁻¹ * t * (f : MulAut G) x) h
  group at hh
  simpa only [mul_assoc, zpow_neg_one] using hh.symm

/-- The restriction kernel for a characteristic p-subgroup containing its
centralizer is a p-group. -/
public theorem isPGroup_characteristic_restriction_kernel_of_centralizer_le
    {G : Type*} [Group G] [Finite G]
    (C : Subgroup G) [C.Characteristic] {p : ℕ} (hC : IsPGroup p C)
    (hself : centralizer (C : Set G) ≤ C) :
    IsPGroup p (MulAut.characteristic C).ker := by
  have hle : (MulAut.characteristic C).ker ≤ (automorphismPair C).ker := by
    intro f hf
    change automorphismPair C f = 1
    rw [automorphismPair_apply]
    apply Prod.ext (MonoidHom.mem_ker.mp hf)
    change quotientAut C f = 1
    apply MulEquiv.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H x =>
      change quotientAut C f (QuotientGroup.mk' C x) = QuotientGroup.mk' C x
      rw [quotientAut_apply_mk]
      exact (QuotientGroup.eq.mpr (displacement_mem C hself ⟨f, hf⟩ x)).symm
  exact (isPGroup_automorphism_pair_kernel C hC).to_le hle

end Subgroup
