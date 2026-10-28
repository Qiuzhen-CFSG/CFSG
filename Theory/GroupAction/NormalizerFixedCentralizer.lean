module

public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Fixed subgroups of normalizer actions are relative centralizers

Restriction of ambient conjugation to an invariant subgroup has fixed
subgroup exactly its relative element centralizer. The equivalence below
retains the original elements, and transports the p-residual as well.

This is the interface between intrinsic automorphism models and ambient
centralizer statements, used for the cover calculations in Aschbacher--Smith
15.3.38, printed p.1137 (1 March 2004 manuscript).
-/

public section

namespace Subgroup
variable {G : Type*} [Group G]

/-- The fixed-subgroup equivalence uses the original ambient elements. -/
@[expose] def normalizerFixedEquivCentralizer (L : Subgroup G) (n : normalizer (L : Set G)) :
    (L.normalizerMonoidHom n).fixedSubgroup ≃*
      (L ⊓ centralizer ({(n : G)} : Set G) : Subgroup G) where
  toFun x := ⟨x.val.val, x.val.property, by
    apply mem_centralizer_singleton_iff.mpr
    have hx := congrArg Subtype.val ((MulAut.mem_fixedSubgroup _ _).mp x.property)
    change (n : G) * (x.val : G) * (n : G)⁻¹ = (x.val : G) at hx
    exact (mul_inv_eq_iff_eq_mul.mp hx).symm⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, by
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    apply Subtype.ext
    change (n : G) * x.val * (n : G)⁻¹ = x.val
    rw [← mem_centralizer_singleton_iff.mp x.property.2, mul_inv_cancel_right]⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem normalizerFixedEquivCentralizer_apply (L : Subgroup G)
    (n : normalizer (L : Set G)) (x : (L.normalizerMonoidHom n).fixedSubgroup) :
    ((normalizerFixedEquivCentralizer L n x :
      (L ⊓ centralizer ({(n : G)} : Set G) : Subgroup G)) : G) = ((x : L) : G) := rfl

/-- The same equivalence transports the intrinsic p-residual. -/
noncomputable def normalizerResidualEquivCentralizer (L : Subgroup G)
    (n : normalizer (L : Set G)) (p : ℕ) :
    pResidual p (L.normalizerMonoidHom n).fixedSubgroup ≃*
      pResidual p (L ⊓ centralizer ({(n : G)} : Set G) : Subgroup G) := by
  let e := normalizerFixedEquivCentralizer L n
  exact ((pResidual p _).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (map_pResidual p e))
end Subgroup
