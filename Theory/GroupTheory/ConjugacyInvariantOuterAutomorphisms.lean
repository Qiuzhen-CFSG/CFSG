module

public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.PGroup

/-!
# Outer automorphisms detected on a conjugacy-invariant subgroup

Suppose every automorphism of G takes H to a G-conjugate, Out(H) is a
p-group, and automorphisms fixing H pointwise are inner. Then Out(G) is a
p-group. Normalize an automorphism to preserve H, take a p-power whose
restriction is inner, and remove that inner restriction by conjugation
with an element of H. The remaining automorphism belongs to the pointwise
kernel. All conjugations used disappear in Out(G).

This elementary restriction argument is used for the M23 entry of GLS3,
Table 5.3d, and the outer-group inspection in Aschbacher–Smith, printed p.510.
The normalization and pointwise-kernel premises are explicit obligations.
-/

namespace MulAut
open Subgroup
open scoped Pointwise

/-- Restriction to a subgroup invariant up to inner conjugacy detects the
outer p-group property when the pointwise kernel is inner. -/
public theorem isPGroup_outer_of_conjugacy_invariant_subgroup
    {G : Type*} [Group G] (H : Subgroup G) (p : ℕ)
    (hconj : ∀ a : MulAut G, ∃ g : G, (MulAut.conj g * a) • H = H)
    (hlocal : IsPGroup p (Outer H))
    (hfix : ∀ a : MulAut G, (∀ x ∈ H, a x = x) → a ∈ innerSubgroup G) :
    IsPGroup p (Outer G) := by
  let A := MulAction.stabilizer (MulAut G) H
  let r : A →* MulAut H :=
    { toFun := fun a => (a.val.subgroupMap H).trans
        (MulEquiv.subgroupCongr a.property)
      map_one' := by ext x; rfl
      map_mul' := by intro a b; ext x; rfl }
  let q := QuotientGroup.mk' (innerSubgroup G)
  have hi (g : G) : q (MulAut.conj g) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (innerSubgroup G) x
  obtain ⟨g, hg⟩ := hconj a
  let b : A := ⟨MulAut.conj g * a, hg⟩
  obtain ⟨n, hn⟩ := hlocal (QuotientGroup.mk' (innerSubgroup H) (r b))
  have hr : r (b ^ (p ^ n)) ∈ innerSubgroup H := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (innerSubgroup H) (r (b ^ (p ^ n))) = 1
    rwa [map_pow, map_pow]
  obtain ⟨c, hc⟩ := hr
  let d : MulAut G := MulAut.conj (c : G)⁻¹ * (b.val ^ (p ^ n))
  have hd : d ∈ innerSubgroup G := by
    apply hfix
    intro y hy
    have he := congrArg (fun f : MulAut H => ((f ⟨y, hy⟩ : H) : G)) hc
    change (c : G) * y * (c : G)⁻¹ = (b.val ^ (p ^ n)) y at he
    change (c : G)⁻¹ * ((b.val ^ (p ^ n)) y) * ((c : G)⁻¹)⁻¹ = y
    rw [← he]
    group
  have hdq : q d = 1 := (QuotientGroup.eq_one_iff _).mpr hd
  have hbq : q b.val = q a := by
    change q (MulAut.conj g * a) = q a
    rw [map_mul, hi, one_mul]
  refine ⟨n, ?_⟩
  change q a ^ (p ^ n) = 1
  simpa only [d, map_mul, hi, one_mul, map_pow, hbq] using hdq

end MulAut
