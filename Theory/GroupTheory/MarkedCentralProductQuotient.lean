module

public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Marked center quotients of internal central products

For commuting subgroups with an ordered product decomposition, multiplication
identifies the ambient center quotient with the product of the factor center
quotients. The evaluation formula retains both original inclusions. Compare
the kernels of multiplication followed by the ambient quotient and of the
product of the factor quotient maps.

Source: Aschbacher–Smith A.2.12(II), printed p.37. The kernel argument also
appears in the moving-component calculation of 13.6.6.
-/

public section
namespace Subgroup
variable {H : Type*} [Group H]

/-- The central quotient comparison, with the two factor projections specified. -/
theorem exists_centerQuotient_product_equiv (K J : Subgroup H) (hc : K ≤ centralizer (J : Set H))
    (hprod : ∀ h : H, ∃ k : K, ∃ j : J, (k : H) * j = h) :
    ∃ e : (H ⧸ center H) ≃* ((K ⧸ center K) × (J ⧸ center J)),
      ∀ (k : K) (j : J),
        e (QuotientGroup.mk' (center H)
          ((k : H) * j)) =
        (QuotientGroup.mk' (center K) k, QuotientGroup.mk' (center J) j) := by
  have hcomm (k : K) (j : J) : Commute (k : H) (j : H) :=
    (hc k.property j j.property).symm
  let f : K × J →* H := K.subtype.noncommCoprod J.subtype hcomm
  have hf : Function.Surjective f := by
    intro h
    obtain ⟨k, j, rfl⟩ := hprod h
    exact ⟨(k, j), rfl⟩
  let F := (QuotientGroup.mk' (center H)).comp f
  let Q := (QuotientGroup.mk' (center K)).prodMap (QuotientGroup.mk' (center J))
  have hF : Function.Surjective F := (QuotientGroup.mk'_surjective _).comp hf
  have hQ : Function.Surjective Q := by
    rintro ⟨x, y⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (center K) x
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (center J) y
    exact ⟨(k, j), rfl⟩
  have hker : F.ker = Q.ker := by
    ext ⟨k, j⟩
    change QuotientGroup.mk' (center H) (f (k, j)) = 1 ↔
      (QuotientGroup.mk' (center K) k, QuotientGroup.mk' (center J) j) = (1, 1)
    rw [Prod.mk.injEq]
    simp only [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro hz
      constructor
      · apply mem_center_iff.mpr
        intro x
        apply Subtype.ext
        have he := mem_center_iff.mp hz (x : H)
        change (x : H) * ((k : H) * j) = ((k : H) * j) * x at he
        have hxj := (hcomm x j).eq
        have hkx : (x : H) * k = (k : H) * x := by
          apply mul_right_cancel (b := (j : H))
          simpa only [mul_assoc, ← hxj] using he
        exact hkx
      · apply mem_center_iff.mpr
        intro y
        apply Subtype.ext
        have he := mem_center_iff.mp hz (y : H)
        change (y : H) * ((k : H) * j) = ((k : H) * j) * y at he
        have hky := (hcomm k y).eq
        apply mul_left_cancel (a := (k : H))
        simpa only [Subgroup.coe_mul, ← mul_assoc, ← hky] using he
    · rintro ⟨hk, hj⟩
      apply mem_center_iff.mpr
      intro x
      obtain ⟨⟨u, v⟩, rfl⟩ := hf x
      change ((u : H) * v) * ((k : H) * j) = ((k : H) * j) * ((u : H) * v)
      have huk : Commute (u : H) k := (show Commute u k from mem_center_iff.mp hk u).map K.subtype
      have hvj : Commute (v : H) j := (show Commute v j from mem_center_iff.mp hj v).map J.subtype
      exact (huk.mul_left (hcomm k v).symm).mul_right ((hcomm u j).mul_left hvj) |>.eq
  let e := (QuotientGroup.quotientKerEquivOfSurjective F hF).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective Q hQ))
  refine ⟨e, fun k j => ?_⟩
  change e (F (k, j)) = Q (k, j)
  change (QuotientGroup.quotientKerEquivOfSurjective Q hQ)
    (QuotientGroup.quotientMulEquivOfEq hker
      ((QuotientGroup.quotientKerEquivOfSurjective F hF).symm (F (k, j)))) = _
  rw [show F (k, j) = QuotientGroup.quotientKerEquivOfSurjective F hF
    (QuotientGroup.mk' F.ker (k, j)) from rfl, MulEquiv.symm_apply_apply]
  rfl


end Subgroup
