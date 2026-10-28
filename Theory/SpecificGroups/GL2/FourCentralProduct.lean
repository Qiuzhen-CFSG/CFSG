module
public import Theory.SpecificGroups.GL2.FourDerived
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The marked central product of GL₂(4)

The product map is the actual scalar matrix times the actual determinant-one
matrix. Its kernel is trivial because the scalar unit has both square and
cube one. Thus the full matrix group is C₃ × A₅, with its original matrices
retained, rather than merely recognized by its order.
-/

public noncomputable section
namespace Representation.SL2FourNatural.SemilinearNormalizer
open Matrix Subgroup

def productHom : Fˣ × SL →* LinearGroup :=
  (GeneralLinearGroup.scalar (Fin 2)).noncommCoprod SpecialLinearGroup.toGL
    (fun z x => GeneralLinearGroup.scalar_commute z (SpecialLinearGroup.toGL x))

theorem product_injective : Function.Injective productHom := by
  apply (injective_iff_map_eq_one _).mpr
  rintro ⟨z,x⟩ hx
  have hd : GeneralLinearGroup.det (SpecialLinearGroup.toGL x) = (1 : Fˣ) := by
    apply Units.ext
    exact x.property
  have hz2 : z^2=1 := by
    have hh := congrArg GeneralLinearGroup.det hx
    change GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 2) z *
      SpecialLinearGroup.toGL x) = GeneralLinearGroup.det 1 at hh
    simpa only [map_mul,map_one,GeneralLinearGroup.det_scalar,Fintype.card_fin,hd,mul_one] using hh
  have hz3 : z^3=1 := by
    have hc : Nat.card Fˣ=3 := by
      rw [Nat.card_units,Nat.card_eq_fintype_card,card_field]
    exact hc ▸ pow_card_eq_one'
  have hz : z=1 := (pow_eq_one_iff_of_coprime (by decide : Nat.Coprime 2 3)).mp ⟨hz2,hz3⟩
  have hx1 : SpecialLinearGroup.toGL x = (1 : LinearGroup) := by
    change GeneralLinearGroup.scalar (Fin 2) z * SpecialLinearGroup.toGL x = 1 at hx
    simpa only [hz,map_one,one_mul] using hx
  exact Prod.ext hz (SpecialLinearGroup.toGL_injective (hx1.trans (map_one _).symm))

/-- Literal scalar times special-linear coordinates on the full GL₂(4). -/
@[expose] def scalarSpecialEquiv : Fˣ × SL ≃* LinearGroup :=
  MulEquiv.ofBijective productHom ((Nat.bijective_iff_injective_and_card productHom).mpr
    ⟨product_injective,by
      rw [Nat.card_prod,Nat.card_units,Nat.card_eq_fintype_card,card_field,
        Nat.card_congr alternatingFiveEquiv.toEquiv,nat_card_alternatingGroup]
      rw [Matrix.card_GL_field]
      norm_num [Nat.card_eq_fintype_card,card_field,Nat.factorial,Fin.prod_univ_succ]⟩)

/-- Coordinates retain the actual scalar and determinant-one embeddings. -/
theorem scalarSpecialEquiv_apply (z : Fˣ) (x : SL) :
    scalarSpecialEquiv (z,x) = GeneralLinearGroup.scalar (Fin 2) z * SpecialLinearGroup.toGL x := by
  change productHom (z,x) = _
  rfl

/-- The full group is a product with the cubic center, retaining all of GL₂(4). -/
@[expose] def cubicFiveEquiv : LinearGroup ≃* Multiplicative (ZMod 3) × alternatingGroup (Fin 5) :=
  scalarSpecialEquiv.symm.trans (MulEquiv.prodCongr
    (mulEquivOfCyclicCardEq (by
      rw [Nat.card_units,Nat.card_eq_fintype_card,card_field]
      simp [Nat.card_eq_fintype_card,Fintype.card_multiplicative])) alternatingFiveEquiv)
end Representation.SL2FourNatural.SemilinearNormalizer
