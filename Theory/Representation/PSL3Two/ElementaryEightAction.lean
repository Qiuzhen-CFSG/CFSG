module

public import Theory.ElementaryAbelian.AutomorphismLinearModelEight
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel

/-!
# Recognizing faithful actions on an elementary abelian group of order eight

Every faithful SL₃(2) action on an elementary abelian group of order eight
is the natural action after an automorphism of SL₃(2). A basis identifies
the group with the binary three-space. Conjugating the action into matrices
then gives an injective endomorphism of SL₃(2), hence an automorphism.
The equivalence and marking satisfy the actual matrix action equation.

This elementary recognition is used for the quotient in Meierfrankenfeld--
Stellmacher, *Pushing up weak BN-pairs of rank two* (1993), (3.6), p.870.
The marking is independent of any marking on another module.
-/

public section

open scoped IsMulCommutative
open Matrix

namespace Matrix.PSL3Two

/-- A faithful action on an elementary eight-group has a natural matrix model,
with its own automorphism marking. -/
theorem exists_natural_marking (E : Type*) [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hcard : Nat.card E = 8)
    (a : Matrix.PSL3Two.SL →* MulAut E) (hinj : Function.Injective a) :
    ∃ (e : E ≃* Multiplicative (Fin 3 → ZMod 2))
      (marking : Matrix.PSL3Two.SL ≃* Matrix.PSL3Two.SL),
      ∀ g x, (e (a g x)).toAdd = (marking g).val.mulVec (e x).toAdd := by
  classical
  have hpow : 2 ^ Module.finrank (ZMod 2) (Additive E) = 2 ^ 3 := by
    have hsize := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive E)
    change Nat.card E = _ at hsize
    simpa only [Nat.card_zmod, hcard, show (2 : ℕ) ^ 3 = 8 by decide] using hsize.symm
  have hdim : Module.finrank (ZMod 2) (Additive E) = 3 :=
    Nat.pow_right_injective (by decide : 1 < 2) hpow
  let b := Module.finBasisOfFinrankEq (ZMod 2) (Additive E) hdim
  let e := b.equivFun
  let l : Matrix.PSL3Two.SL →* ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) := {
    toFun := fun g => (e.symm.trans
      ({ (a g).toAdditive with map_smul' := ZMod.map_smul (a g).toAdditive } :
        Additive E ≃ₗ[ZMod 2] Additive E)).trans e
    map_one' := by ext v; simp
    map_mul' := by intro g h; ext v; simp }
  let toGL := (LinearMap.GeneralLinearGroup.generalLinearEquiv
      (ZMod 2) (Fin 3 → ZMod 2)).symm.trans Matrix.GeneralLinearGroup.toLin.symm
  let f : Matrix.PSL3Two.SL →* Matrix.PSL3Two.SL :=
    Matrix.PSL3Two.equivGL.symm.toMonoidHom.comp (toGL.toMonoidHom.comp l)
  have hf (g : Matrix.PSL3Two.SL) (v : Fin 3 → ZMod 2) :
      (f g).val.mulVec v = l g v := by
    have heq : Matrix.SpecialLinearGroup.toGL (f g) = toGL (l g) := by
      dsimp only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [← Matrix.PSL3Two.equivGL_apply, MulEquiv.apply_symm_apply]
    have hh := congrArg (fun t : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) =>
      (Matrix.GeneralLinearGroup.toLin t : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)) v) heq
    simp only [toGL, MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at hh
    change (f g).val.mulVec v =
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 3 → ZMod 2)
        ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 3 → ZMod 2)).symm
          (l g))) v at hh
    simpa only [MulEquiv.apply_symm_apply] using hh
  have hfi : Function.Injective f := by
    intro g h hgh
    apply hinj
    ext x
    apply Additive.ofMul.injective
    apply e.injective
    have hh := congrArg (fun t : Matrix.PSL3Two.SL =>
      t.val.mulVec (e (Additive.ofMul x))) hgh
    simpa [hf, l, MulEquiv.toAdditive] using hh
  let eg : E ≃* Multiplicative (Fin 3 → ZMod 2) := {
    toFun := fun x => Multiplicative.ofAdd (e (Additive.ofMul x))
    invFun := fun v => (e.symm v.toAdd).toMul
    left_inv := fun x => e.symm_apply_apply x
    right_inv := fun v => e.apply_symm_apply v
    map_mul' := fun x y => e.map_add x y }
  refine ⟨eg, MulEquiv.ofBijective f ⟨hfi, Finite.surjective_of_injective hfi⟩, ?_⟩
  intro g x
  change e (Additive.ofMul (a g x)) = (f g).val.mulVec (e (Additive.ofMul x))
  rw [hf]
  simp [l]

end Matrix.PSL3Two
