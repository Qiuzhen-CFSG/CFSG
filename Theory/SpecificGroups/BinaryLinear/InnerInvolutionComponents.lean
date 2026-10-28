module

public import Theory.SpecificGroups.BinaryLinear.Parabolics
public import Theory.GroupAction.AutomorphismFixedTransport
public import Theory.GroupTheory.GeneralizedFitting.ComponentExclusion

/-!
# Ordinary components in binary involution centralizers

For a nonidentity involution t on a binary vector space, put W = range(t - 1).
The square-zero displacement shows that t fixes W. Every element fixing W
pointwise and acting trivially modulo W centralizes t. This entire parabolic
radical is normal in the centralizer of t and self-centralizing in the full
linear group. Thus the involution centralizer has self-centralizing two-core
and, for finite V, has no ordinary component.

No involution table or identification of a residual quotient is needed.
Source: the defining binary linear action; used in the PSL₅(2) inspection in
Aschbacher–Smith, proof of 15.3.38, printed p.1137, and Theorem C(4), p.33.
-/

public section

open Subgroup Theory.GroupTheory
namespace BinaryLinear
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Every nonidentity binary involution has a centralizer of characteristic two. -/
theorem inner_involution_twoCore (t : BinaryLinear.GL V) (ht : t ^ 2 = 1) (ht1 : t ≠ 1) :
    centralizer (pCore 2 (MulAut.conj t).fixedSubgroup :
      Set (MulAut.conj t).fixedSubgroup) ≤ pCore 2 (MulAut.conj t).fixedSubgroup := by
  let N := t.toLinearMap - LinearMap.id
  let W := LinearMap.range N
  have htt (v : V) : t (t v) = v := by
    exact congrArg (fun g : BinaryLinear.GL V => g v) ht
  have hneg (v : V) : -v = v := by
    have hh : (-(1 : ZMod 2)) = 1 := by decide
    calc
      -v = (-(1 : ZMod 2)) • v := (neg_one_smul (ZMod 2) v).symm
      _ = v := by rw [hh, one_smul]
  have hfixed (w : V) (hw : w ∈ W) : t w = w := by
    obtain ⟨v, rfl⟩ := hw
    change t (t v - v) = t v - v
    rw [map_sub, htt]
    simp only [sub_eq_add_neg, hneg, add_comm]
  have hW0 : W ≠ ⊥ := by
    intro h
    apply ht1
    ext v
    have hv : t v - v ∈ W := LinearMap.mem_range_self N v
    rw [h, Submodule.mem_bot] at hv
    exact sub_eq_zero.mp hv
  have hWt : W ≠ ⊤ := by
    intro h
    apply ht1
    ext v
    exact hfixed v (h.symm ▸ Submodule.mem_top)
  have hRC : radical W ≤ (MulAut.conj t).fixedSubgroup := by
    intro g hg
    rw [MulAut.mem_fixedSubgroup, MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
    ext v
    change t (g v) = g (t v)
    have h1 := hfixed (g v - v) (hg.2 v)
    have h2 := hg.1 (t v - v) (LinearMap.mem_range_self N v)
    rw [map_sub] at h1 h2
    calc
      t (g v) = (g v - v) + t v := eq_add_of_sub_eq h1
      _ = (t v - v) + g v := by abel
      _ = g (t v) := (eq_add_of_sub_eq h2).symm
  have hCP : (MulAut.conj t).fixedSubgroup ≤ parabolic W := by
    intro g hg v
    have hc : t * g = g * t := mul_inv_eq_iff_eq_mul.mp
      ((MulAut.mem_fixedSubgroup _ _).mp hg)
    have he (x : V) : g (N x) = N (g x) := by
      change g (t x - x) = t (g x) - g x
      rw [map_sub]
      exact congrArg (fun z : V => z - g x) (congrArg (fun a : BinaryLinear.GL V => a x) hc).symm
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨g.symm x, g.injective ?_⟩
      rw [he, g.apply_symm_apply]
      exact hx
    · rintro ⟨x, rfl⟩
      exact ⟨g x, (he x).symm⟩
  exact centralizer_pCore_le_of_normalized 2 (radical W) _ (radical_two W)
    hRC (hCP.trans (parabolic_le_normalizer W)) (centralizer_radical_le hW0 hWt)
/-- A binary involution centralizer has no ordinary component, even when a
PSL₃(2) section acts on its normal two-subgroup. -/
theorem inner_involution_no_component [Finite V] (t : BinaryLinear.GL V)
    (ht : t ^ 2 = 1) (ht1 : t ≠ 1)
    (D : Subgroup (MulAut.conj t).fixedSubgroup) :
    ¬ IsComponent (MulAut.conj t).fixedSubgroup D := by
  let : Finite (BinaryLinear.GL V) :=
    Finite.of_injective (fun g : BinaryLinear.GL V => (g : V → V)) DFunLike.coe_injective
  exact not_isComponent_of_twoCore (inner_involution_twoCore t ht ht1) D

end BinaryLinear
