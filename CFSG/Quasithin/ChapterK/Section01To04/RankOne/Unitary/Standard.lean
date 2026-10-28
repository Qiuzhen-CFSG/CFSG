module
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Unitary.Model
public import Theory.Representation.GeneralLinearNatural

/-!
# Changing the Hermitian basis of the marked natural module

The group identification changes by C⁻¹gC and the module coordinates by C⁻¹.
Thus a genuine natural model for any nonsingular Hermitian form supplies the
antidiagonal model used by the root calculation, with the same field involution.
Source: Huppert II.10.4(b); Aschbacher–Smith, K.3.3, printed p.456.
-/

public section
namespace CFSG.Quasithin.ChapterK.RankOne.UnitaryModel
open BenderSuzuki.MatrixGroups Matrix
open HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport
variable {G V F : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [Field F] [Algebra (ZMod 2) F]
  {J : HermitianForm 3 F} {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- Simultaneous change of the group and column coordinates. -/
noncomputable def changeBasis (M : UnitaryModel J ρ L) (C : GL (Fin 3) F)
    (hC : J.conjTranspose C.val * J.form * C.val = (standardForm J).form) :
    UnitaryModel (standardForm J) ρ L where
  groupEquiv := M.groupEquiv.trans (specialEquiv J C hC)
  coordinates := M.coordinates.trans
    ((LinearMap.GeneralLinearGroup.toLinearEquiv (Matrix.GeneralLinearGroup.toLin C⁻¹)).restrictScalars (ZMod 2))
  intertwines := by
    intro g v
    simp only [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
      MulEquiv.trans_apply, specialEquiv_apply]
    change (C⁻¹).val.mulVec (M.coordinates (ρ (g : G) v)) =
      (C⁻¹ * (M.groupEquiv g).val * C).val.mulVec ((C⁻¹).val.mulVec (M.coordinates v))
    rw [M.intertwines, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    change (C⁻¹ * (M.groupEquiv g).val).val =
      ((C⁻¹ * (M.groupEquiv g).val * C) * C⁻¹).val
    simp only [mul_inv_cancel_right]

/-- No standard Gram-matrix assumption is needed to obtain standard natural coordinates. -/
theorem exists_standard [Finite F] (M : UnitaryModel J ρ L)
    {s : ℕ} (hs : 0 < s) (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hconj : ∀ x : F, J.conj x = x ^ (2 ^ s)) :
    Nonempty (UnitaryModel (standardForm J) ρ L) := by
  obtain ⟨C, hC⟩ := exists_standard_basis J (2 ^ s) hcard
    (FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 s hs hcard hconj)
  exact ⟨M.changeBasis C hC⟩

end CFSG.Quasithin.ChapterK.RankOne.UnitaryModel
