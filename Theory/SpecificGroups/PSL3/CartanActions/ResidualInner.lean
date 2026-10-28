module

public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions
public import Theory.SpecificGroups.PSL3.ProjectionKernel
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# Removing the diagonal contribution of a two-power linear actor

A scalar determinant correction makes the cube of every GL₃ actor inner.
Coprimality of three and a two-power order bound therefore makes that actor
inner. On SL₃, perfectness detects innerness through its actual central
quotient, retaining the scalar kernel rather than identifying the carriers.

Source: Aschbacher–Smith 13.8.20, printed p.954; GLS3 §2.7. The determinant
correction generalizes SevenAction.Inner. The imported ATLAS perfection
proof retains its source attribution and license.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3.CartanActions.ResidualInner
open Matrix.PSL3.OuterSolvable
variable {F : Type*} [Field F]
private theorem linearConj_scalar (u : Fˣ) :
    linearConj F (GeneralLinearGroup.scalar (Fin 3) u) = 1 := by
  ext y
  obtain ⟨x, rfl⟩ := Matrix.PSL3.projection_surjective F y
  change QuotientGroup.mk (linearConjSL F (GeneralLinearGroup.scalar (Fin 3) u) x) =
    QuotientGroup.mk x
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [linearConjSL_toGL, GeneralLinearGroup.scalar_commute, mul_inv_cancel_right]

theorem linearConj_cube_inner (g : GL (Fin 3) F) :
    linearConj F g ^ 3 ∈ MulAut.innerSubgroup PSL(3,F) := by
  let m := GeneralLinearGroup.scalar (Fin 3) (GeneralLinearGroup.det g)⁻¹ * g ^ 3
  have hm : GeneralLinearGroup.det m = 1 := by
    simp only [m, map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin, map_pow,
      inv_pow, inv_mul_cancel]
  let x := (slEquivDetKernel F).symm ⟨m, hm⟩
  refine ⟨Matrix.PSL3.projection F x, ?_⟩
  calc
    MulAut.conj (Matrix.PSL3.projection F x) = linearConj F (SpecialLinearGroup.toGL x) :=
      (linearConj_toGL F x).symm
    _ = linearConj F m := by rw [slEquivDetKernel_symm_toGL]
    _ = _ := by
      dsimp only [m]
      rw [map_mul, linearConj_scalar, one_mul, map_pow]

theorem linearConj_twoPower_inner (g : GL (Fin 3) F) {k : ℕ}
    (hpow : linearConj F g ^ (2 ^ k) = 1) :
    linearConj F g ∈ MulAut.innerSubgroup PSL(3,F) := by
  apply (Subgroup.zpowers_le.mpr (linearConj_cube_inner g))
  apply mem_zpowers_pow_iff.mpr
  exact ((show Nat.Coprime 3 2 by decide).pow_right k).of_dvd_right
    (orderOf_dvd_of_pow_eq_one hpow)

theorem special_inner_of_projective_inner (α : MulAut SL(3,F))
    (hi : centerAction F α ∈ MulAut.innerSubgroup PSL(3,F)) :
    α ∈ MulAut.innerSubgroup SL(3,F) := by
  let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
  have he : centerAction F = MulAut.centralQuotientAction (MulEquiv.refl PSL(3,F)) := by
    ext a x
    obtain ⟨y,rfl⟩ := Matrix.PSL3.projection_surjective F x
    change centerAction F a (QuotientGroup.mk y) =
      MulAut.centralQuotientAction (MulEquiv.refl PSL(3,F)) a
        ((MulEquiv.refl PSL(3,F)) (QuotientGroup.mk' (center SL(3,F)) y))
    rw [centerAction_mk, MulAut.centralQuotientAction_apply]
    rfl
  obtain ⟨y,hy⟩ := hi
  have hi' : ∃ y, MulAut.centralQuotientAction (MulEquiv.refl PSL(3,F)) α = MulAut.conj y := by
    exact ⟨y, by rw [← he]; exact hy.symm⟩
  obtain ⟨x,hx⟩ := (MulAut.centralQuotientAction_inner_iff (MulEquiv.refl PSL(3,F)) α).mp hi'
  exact ⟨x,hx.symm⟩
end Matrix.PSL3.CartanActions.ResidualInner
