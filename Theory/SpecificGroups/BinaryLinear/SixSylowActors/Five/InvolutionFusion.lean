module

public import Theory.SpecificGroups.BinaryLinear.SixSylowActors.Five.FixedGeometry
public import Theory.GroupAction.AutomorphismFixedTransport
/-!
# Fusion in the outer involution coset of PSL₅(2)

Symmetric Gram factorization conjugates every outer involution of the binary
five-dimensional linear group to inverse transpose by an element of that
same linear group. Apply this to an involution and its inner twist. Triviality
of the binary scalar center turns the resulting equality of conjugations
into the precise coboundary identity for the twisting element.

This retains an actual group element as conjugator. It therefore gives fusion
in every ambient group inducing the specified action, rather than only
conjugacy in the automorphism group.

Source: Aschbacher–Smith 2.5.19(4), printed p.562, using the binary
inverse-transpose calculation in E.6.23, printed p.254.
-/

public section
open Subgroup Theory.GroupTheory
open BinaryLinear.OuterCyclic
namespace BinaryLinear.SixSylowActors.Five
private theorem graph_normalize (a : MulAut (LinearGroup 5))
    (ha : a ^ 2 = 1) (hout : a ∉ MulAut.innerSubgroup (LinearGroup 5)) :
    ∃ h : LinearGroup 5, MulAut.conj h * a * (MulAut.conj h)⁻¹ = graphLinear 5 := by
  obtain ⟨g, hs, rfl⟩ := exists_symmetric_twist a ha hout
  obtain ⟨h, hh⟩ := symmetric_gram g hs
  refine ⟨slEquivLinear 5 h, ?_⟩
  apply MulEquiv.ext
  intro x
  change MulAut.conj (slEquivLinear 5 h)
    ((graphLinear 5 * MulAut.conj (slEquivLinear 5 g))
      ((MulAut.conj (slEquivLinear 5 h))⁻¹ x)) = graphLinear 5 x
  rw [gram_intertwines g h hh]
  simp
  group

private theorem binary_inner_conjugate (a b : MulAut (LinearGroup 5))
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (haout : a ∉ MulAut.innerSubgroup (LinearGroup 5))
    (hbout : b ∉ MulAut.innerSubgroup (LinearGroup 5)) :
    ∃ w : LinearGroup 5, MulAut.conj w * a * (MulAut.conj w)⁻¹ = b := by
  obtain ⟨h, hh⟩ := graph_normalize a ha haout
  obtain ⟨k, hk⟩ := graph_normalize b hb hbout
  refine ⟨k⁻¹ * h, ?_⟩
  rw [map_mul, map_inv]
  calc
    _ = (MulAut.conj k)⁻¹ * (MulAut.conj h * a * (MulAut.conj h)⁻¹) * MulAut.conj k := by group
    _ = (MulAut.conj k)⁻¹ * (MulAut.conj k * b * (MulAut.conj k)⁻¹) * MulAut.conj k := by rw [hh, hk]
    _ = b := by group

private theorem twist_coboundary_of_inner_conjugate {E : Type*} [Group E]
    (hz : center E = ⊥) (a : MulAut E) (x w : E)
    (hw : MulAut.conj w * a * (MulAut.conj w)⁻¹ = MulAut.conj x * a) :
    x = w * (a w)⁻¹ := by
  apply MulAut.conj_injective_of_center_eq_bot hz
  have he : MulAut.conj (w * (a w)⁻¹) =
      (MulAut.conj w * a * (MulAut.conj w)⁻¹) * a⁻¹ := by
    rw [← map_inv MulAut.conj w]
    apply MulEquiv.ext
    intro y
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, MulAut.conj_symm_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply]
  rw [he, hw]
  group

private theorem twist_sq {E : Type*} [Group E]
    (a : MulAut E) (ha : a ^ 2 = 1) (x : E) (hx : x * a x = 1) :
    (MulAut.conj x * a) ^ 2 = 1 := by
  have haa (y : E) : a (a y) = y := congrArg (fun b : MulAut E => b y) ha
  apply MulEquiv.ext
  intro y
  change x * a (x * a y * x⁻¹) * x⁻¹ = y
  simp only [map_mul, map_inv, haa]
  calc
    _ = (x * a x) * y * (x * a x)⁻¹ := by group
    _ = y := by rw [hx]; simp

/-- Every cocycle for an outer involution of the binary degree-five group is
an actual coboundary, with a conjugator in that group. -/
theorem binary_cocycle_coboundary
    (a : MulAut (LinearGroup 5)) (ha : a ^ 2 = 1)
    (hout : a ∉ MulAut.innerSubgroup (LinearGroup 5))
    (x : LinearGroup 5) (hx : x * a x = 1) :
    ∃ w : LinearGroup 5, x = w * (a w)⁻¹ := by
  have hb : MulAut.conj x * a ∉ MulAut.innerSubgroup (LinearGroup 5) := by
    intro hi
    apply hout
    have hh := (MulAut.innerSubgroup (LinearGroup 5)).mul_mem
      ((MulAut.innerSubgroup (LinearGroup 5)).inv_mem (show MulAut.conj x ∈
        MulAut.innerSubgroup (LinearGroup 5) from ⟨x, rfl⟩)) hi
    simpa only [inv_mul_cancel_left] using hh
  obtain ⟨w, hw⟩ := binary_inner_conjugate a (MulAut.conj x * a) ha
    (twist_sq a ha x hx) hout hb
  refine ⟨w, twist_coboundary_of_inner_conjugate ?_ a x w hw⟩
  apply eq_bot_iff.mpr
  intro y hy
  have hh : (slEquivLinear 5).symm y ∈ center (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) := by
    apply mem_center_iff.mpr
    intro k
    apply (slEquivLinear 5).injective
    simpa only [map_mul, MulEquiv.apply_symm_apply] using mem_center_iff.mp hy ((slEquivLinear 5) k)
  have he : (slEquivLinear 5).symm y = 1 := by
    simpa only [binary_center_eq_bot (by decide : 0 < 5), mem_bot] using hh
  apply mem_bot.mpr
  exact (slEquivLinear 5).symm.injective (by simpa using he)



end BinaryLinear.SixSylowActors.Five
