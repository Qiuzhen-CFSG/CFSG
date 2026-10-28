module

public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.Sylow

/-!
# Controlling outer automorphisms on a Sylow subgroup

Suppose the automorphism group of a Sylow p-subgroup is a p-group, and every
automorphism fixing that Sylow subgroup pointwise is inner. Then the outer
automorphism group is a p-group. Sylow conjugacy gives a representative of
each outer class preserving the chosen Sylow subgroup. A p-power of its
restriction is trivial, so that power of the representative is inner.

This is the Sylow-conjugacy reduction used for the Mathieu outer-group
inspection in Aschbacher–Smith, combined 1 March 2004 manuscript, printed
p.510. The two automorphism hypotheses remain explicit model obligations.
-/

namespace MulAut
open Subgroup
open scoped Pointwise

/-- Sylow automorphisms control the outer group when the pointwise kernel is inner. -/
public theorem isPGroup_outer_of_sylow_aut
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hP : IsPGroup p (MulAut P))
    (hfix : ∀ a : MulAut G, (∀ x ∈ (P : Subgroup G), a x = x) →
      a ∈ innerSubgroup G) : IsPGroup p (Outer G) := by
  let H := MulAction.stabilizer (MulAut G) (P : Subgroup G)
  let r : H →* MulAut P :=
    { toFun := fun a => (a.val.subgroupMap (P : Subgroup G)).trans
        (MulEquiv.subgroupCongr a.property)
      map_one' := by ext x; rfl
      map_mul' := by intro a b; ext x; rfl }
  let q := (QuotientGroup.mk' (innerSubgroup G)).comp H.subtype
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (innerSubgroup G) x
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (a • P) P
    have hm : MulAut.conj g * a ∈ H := by
      change (MulAut.conj g * a) • (P : Subgroup G) = (P : Subgroup G)
      rw [mul_smul]
      exact congrArg Sylow.toSubgroup hg
    refine ⟨⟨MulAut.conj g * a, hm⟩, ?_⟩
    change QuotientGroup.mk' (innerSubgroup G) (MulAut.conj g * a) = _
    have hi : QuotientGroup.mk' (innerSubgroup G) (MulAut.conj g) = 1 :=
      (QuotientGroup.eq_one_iff (N := innerSubgroup G) (MulAut.conj g)).mpr ⟨g, rfl⟩
    rw [map_mul, hi, one_mul]
  intro x
  obtain ⟨a, rfl⟩ := hq x
  obtain ⟨n, hn⟩ := hP (r a)
  refine ⟨n, ?_⟩
  rw [← map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  apply hfix
  intro x hx
  have he : r (a ^ (p ^ n)) = 1 := (map_pow r a (p ^ n)).trans hn
  exact congrArg (fun b : MulAut P => ((b ⟨x, hx⟩ : P) : G)) he

end MulAut
