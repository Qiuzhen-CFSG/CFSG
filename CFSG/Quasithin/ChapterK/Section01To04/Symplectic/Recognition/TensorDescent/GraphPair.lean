module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.TensorDescent.Coordinates
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Models
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.NonbinaryRecognition.BinaryDescent.Support
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.FullGroup

/-!
# The quadratic pair is a coefficient-twisted natural tensor

The graph automorphism has period 2r and its power 2s is entrywise 2^s-th
power. When r = 2s, the support pair j,j+r therefore has one common graph
twist and the relative Frobenius twist between its factors. Absorbing the
common twist into the group equivalence gives the literal natural tensor
coefficient-twisted natural model used by K.3.4.

Source: Aschbacher--Smith K.3.4, printed p.456; GLS3, Examples 2.8.10(d).
-/

public section
open Representation
open scoped TensorProduct
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary
namespace CFSG.Quasithin.ChapterK.Symplectic.Recognition.TensorDescent
noncomputable section
variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]

open Theory.SpecificGroups.SymplecticFour
open Fin.NatCast

omit [Finite F] [Algebra (ZMod 2) F] in
private theorem mapCoefficients_id {G ι : Type*} [Group G] [Fintype ι] [DecidableEq ι]
    (τ : Representation F G (ι → F)) : mapCoefficients (RingHom.id F) τ = τ := by
  ext g : 1
  apply LinearMap.toMatrix'.injective
  simp only [mapCoefficients_toMatrix, RingHom.coe_id, Matrix.map_id]

/-- Absorb the common graph power and identify its even difference with Frobenius. -/
def pair_twisted_equiv [CharP F 2] {r s : ℕ} [NeZero (2*r)] (hF : Nat.card F = 2^r)
    (hrs : r = 2*s) (hr : 0 < r) (hq : 2 < Nat.card F)
    (σ : F ≃+* F) (hσ : ∀ x, σ x = x^(2^s)) (j : Fin (2*r)) :
    (tensorModel (RingHom.id F) {j, j + (r : Fin (2*r))}).Equiv
      ((twistedTensor σ).comp
        ((graphDerived F ^ (j : ℕ)).trans (derivedEquivFull_of_card_gt_two hq)).toMonoidHom) := by
  have hj : j ≠ j + (r : Fin (2*r)) := by
    intro hh
    have hz : (r : Fin (2*r)) = 0 := add_left_cancel (hh.symm.trans (add_zero j).symm)
    have hv := congrArg Fin.val hz
    simp only [Fin.val_natCast, Fin.val_zero, Nat.mod_eq_of_lt (by omega : r < 2*r)] at hv
    omega
  have hp : graphDerived F ^ ((j + (r : Fin (2*r)) : Fin (2*r)) : ℕ) =
      graphDerived F ^ (2*s) * graphDerived F ^ (j : ℕ) := by
    rw [Fin.val_add, Fin.val_natCast, Nat.add_mod_mod,
      ← pow_eq_pow_mod _ (graphDerived_pow_field hF), Nat.add_comm, pow_add]
    exact congrArg (fun m : ℕ => graphDerived F ^ m * graphDerived F ^ (j : ℕ)) hrs
  have hsecond (g : Derived F) : basicTwist F ((j + (r : Fin (2*r)) : Fin (2*r)) : ℕ) g =
      symplecticNatural 2 (DiagramAutomorphisms.fieldAutomorphism σ
        (((graphDerived F ^ (j : ℕ)) g).val)) := by
    apply LinearMap.toMatrix'.injective
    change LinearMap.toMatrix' (((graphDerived F ^
      ((j + (r : Fin (2*r)) : Fin (2*r)) : ℕ)) g).val.val.mulVecLin) =
      LinearMap.toMatrix' ((((graphDerived F ^ (j : ℕ)) g).val.val).map σ).mulVecLin
    simp only [← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
    ext a b
    rw [hp]
    change ((graphDerived F ^ (2*s)) ((graphDerived F ^ (j : ℕ)) g)).val.val a b =
      σ (((graphDerived F ^ (j : ℕ)) g).val.val a b)
    rw [graphDerived_even_apply, hσ]
  have heq : (basicTwist F j).tprod (basicTwist F ((j + (r : Fin (2*r)) : Fin (2*r)) : ℕ)) =
      (twistedTensor σ).comp
        ((graphDerived F ^ (j : ℕ)).trans (derivedEquivFull_of_card_gt_two hq)).toMonoidHom := by
    ext g : 1
    change TensorProduct.map (basicTwist F j g) (basicTwist F ((j + (r : Fin (2*r)) : Fin (2*r)) : ℕ) g) = _
    rw [hsecond]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.trans_apply, derivedEquivFull_of_card_gt_two_apply]
    rfl
  have η := tensorModel_pair_equiv (RingHom.id F) j (j + (r : Fin (2*r))) hj
  rw [mapCoefficients_id, mapCoefficients_id, heq] at η
  exact η

end
end CFSG.Quasithin.ChapterK.Symplectic.Recognition.TensorDescent
