module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.ActionAdapter

/-!
# Original displacement centers in literal orthogonal coordinates

The original centralizer quotient acts on its prescribed faithful moved
subrepresentation. A realized commutator line remains nontrivial there by
faithfulness. Exact equivariance then gives its nonzero displacement center
in the binary orthogonal coordinates, retaining the original quotient actor.

Source application: Aschbacher–Smith 10.2.1, printed p.743.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
variable {H : Type*} [Group H]

/-- A realized original commutator line survives faithfully on the prescribed
subrepresentation and in its orthogonal coordinates. -/
theorem orthogonal_displacement_center
    (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (S : Subrepresentation (centralizerQuotient U))
    (hfaith : Function.Injective S.toRepresentation)
    (c : S.toSubmodule ≃ₗ[ZMod 2] BinaryFourPlus.V)
    (ew : (H ⧸ centralizer (U : Set H)) ≃* BinaryFourPlus.Wreath)
    (hw : ∀ x v, c (S.toRepresentation x v) =
      (BinaryFourPlus.wreathToIsometry (ew x)).val (c v))
    (g : H) (u : S.toSubmodule) (hu : (u.val.toMul : H) ≠ 1)
    (hline : ∀ x∈U, ⁅g,x⁆=1 ∨ ⁅g,x⁆=(u.val.toMul : H))
    (hmove : ∃ x∈U, ⁅g,x⁆=(u.val.toMul : H)) :
    let w := ew (QuotientGroup.mk' (centralizer (U : Set H)) g)
    c u ≠ 0 ∧
      (∀ x, (BinaryFourPlus.wreathToIsometry w).val x-x=0 ∨
        (BinaryFourPlus.wreathToIsometry w).val x-x=c u) ∧
      ∃ x, (BinaryFourPlus.wreathToIsometry w).val x-x=c u := by
  let q := QuotientGroup.mk' (centralizer (U : Set H))
  let ρ := S.toRepresentation
  have hi : Function.Injective (fun x : S.toSubmodule => (x.val.toMul : H)) := by
    intro x y he
    exact Subtype.ext (Additive.toMul.injective (Subtype.ext he))
  have hval (x : S.toSubmodule) :
      (((ρ (q g) x-x).val).toMul : H)=⁅g,(x.val.toMul:H)⁆ := by
    change ((centralizerQuotient U (q g) x.val-x.val).toMul:H)=_
    simp only [toMul_sub,div_eq_mul_inv]
    rfl
  have hlineS (x : S.toSubmodule) : ρ (q g) x-x=0 ∨ ρ (q g) x-x=u := by
    rcases hline (x.val.toMul:H) x.val.toMul.property with h | h
    · exact Or.inl (hi ((hval x).trans h))
    · exact Or.inr (hi ((hval x).trans h))
  have hgq : q g ≠ 1 := by
    intro he
    have hc : g ∈ centralizer (U : Set H) :=
      (QuotientGroup.ker_mk' (centralizer (U : Set H))).le he
    obtain ⟨x,hx,he⟩ := hmove
    apply hu
    rw [←he,commutatorElement_eq_one_iff_mul_comm]
    exact (hc x hx).symm
  have hm : ∃ x : S.toSubmodule, ρ (q g) x-x≠0 := by
    by_contra! hh
    apply hgq
    apply hfaith
    apply LinearMap.ext
    intro x
    simpa only [map_one,Module.End.one_apply] using sub_eq_zero.mp (hh x)
  obtain ⟨x,hx⟩ := hm
  have he := (hlineS x).resolve_left hx
  have hc (y : S.toSubmodule) :
      (BinaryFourPlus.wreathToIsometry (ew (q g))).val (c y)-c y = c (ρ (q g) y-y) := by
    rw [map_sub,hw]
  refine ⟨?_,?_,c x,?_⟩
  · intro he
    apply hu
    exact congrArg (fun x : S.toSubmodule => (x.val.toMul:H)) (c.map_eq_zero_iff.mp he)
  · intro y
    obtain ⟨z,rfl⟩ := c.surjective y
    rw [hc]
    exact (hlineS z).imp (fun he => by rw [he,map_zero]) (fun he => congrArg c he)
  · rw [hc,he]

end CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
