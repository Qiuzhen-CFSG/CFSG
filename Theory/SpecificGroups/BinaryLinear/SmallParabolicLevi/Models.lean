module

public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoBlocks
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# Marked small models for the binary Levi factors

Coordinate changes conjugate the actual linear actions. The two-dimensional
factor is identified with S₃ through the checked SL₂(2) projective-line action;
the three-dimensional factor is identified with the actual PSL₃(2) central
quotient. The resulting 2+3 and 3+2 quotient maps retain their factor formulas.

Source application: Aschbacher–Smith 13.8.25, combined manuscript of
1 March 2004, printed pp.959–960 (PDF pp.976–977).
-/

@[expose] public section

namespace BinaryLinear.SmallParabolicLevi
open OuterCyclic
variable {V U : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup U] [Module (ZMod 2) U]

/-- Change linear coordinates in the actual automorphism group. -/
def linearGroupCongr (e : V ≃ₗ[ZMod 2] U) : BinaryLinear.GL V ≃* BinaryLinear.GL U :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm.trans
    ((LinearMap.GeneralLinearGroup.congrLinearEquiv e).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) U))

@[simp] theorem linearGroupCongr_apply (e : V ≃ₗ[ZMod 2] U) (g : BinaryLinear.GL V) (u : U) :
    linearGroupCongr e g u = e (g (e.symm u)) := rfl

/-- The rank-one factor is S₃ via the binary projective-line action. -/
noncomputable def linearTwoEquivSymmetricThree : LinearGroup 2 ≃* Equiv.Perm (Fin 3) :=
  (slEquivLinear 2).symm.trans (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three)

/-- The rank-two factor is the actual central quotient PSL₃(2). -/
noncomputable def linearThreeEquivProjective : LinearGroup 3 ≃*
    Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) :=
  (projectiveEquivLinear (by decide : 0 < 3)).symm

/-- Both block markings survive arbitrary specified coordinates. -/
noncomputable def quotientTwoCoreEquivOfCoordinates [FiniteDimensional (ZMod 2) V]
    (W : Submodule (ZMod 2) V) {r s : ℕ}
    (a : W ≃ₗ[ZMod 2] Space r) (b : (V ⧸ W) ≃ₗ[ZMod 2] Space s) :
    (parabolic W ⧸ pCore 2 (parabolic W)) ≃* LinearGroup r × LinearGroup s :=
  (quotientTwoCoreEquiv W).trans ((linearGroupCongr a).prodCongr (linearGroupCongr b))

@[simp] theorem quotientTwoCoreEquivOfCoordinates_mk [FiniteDimensional (ZMod 2) V]
    (W : Submodule (ZMod 2) V) {r s : ℕ}
    (a : W ≃ₗ[ZMod 2] Space r) (b : (V ⧸ W) ≃ₗ[ZMod 2] Space s)
    (g : parabolic W) :
    quotientTwoCoreEquivOfCoordinates W a b (QuotientGroup.mk' _ g) =
      (linearGroupCongr a (subspaceAction W g), linearGroupCongr b (quotientAction W g)) := rfl

/-- A 2+3 subspace stabilizer has the marked quotient S₃ × PSL₃(2). -/
noncomputable def quotientTwoCoreEquivTwoThree [FiniteDimensional (ZMod 2) V]
    (W : Submodule (ZMod 2) V)
    (a : W ≃ₗ[ZMod 2] Space 2) (b : (V ⧸ W) ≃ₗ[ZMod 2] Space 3) :
    (parabolic W ⧸ pCore 2 (parabolic W)) ≃*
      Equiv.Perm (Fin 3) × Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) :=
  (quotientTwoCoreEquivOfCoordinates W a b).trans
    (linearTwoEquivSymmetricThree.prodCongr linearThreeEquivProjective)

@[simp] theorem quotientTwoCoreEquivTwoThree_mk [FiniteDimensional (ZMod 2) V]
    (W : Submodule (ZMod 2) V)
    (a : W ≃ₗ[ZMod 2] Space 2) (b : (V ⧸ W) ≃ₗ[ZMod 2] Space 3)
    (g : parabolic W) :
    quotientTwoCoreEquivTwoThree W a b (QuotientGroup.mk' _ g) =
      (linearTwoEquivSymmetricThree (linearGroupCongr a (subspaceAction W g)),
       linearThreeEquivProjective (linearGroupCongr b (quotientAction W g))) := rfl

/-- A 3+2 subspace stabilizer has the marked quotient PSL₃(2) × S₃. -/
noncomputable def quotientTwoCoreEquivThreeTwo [FiniteDimensional (ZMod 2) V]
    (W : Submodule (ZMod 2) V)
    (a : W ≃ₗ[ZMod 2] Space 3) (b : (V ⧸ W) ≃ₗ[ZMod 2] Space 2) :
    (parabolic W ⧸ pCore 2 (parabolic W)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) × Equiv.Perm (Fin 3) :=
  (quotientTwoCoreEquivOfCoordinates W a b).trans
    (linearThreeEquivProjective.prodCongr linearTwoEquivSymmetricThree)

@[simp] theorem quotientTwoCoreEquivThreeTwo_mk [FiniteDimensional (ZMod 2) V]
    (W : Submodule (ZMod 2) V)
    (a : W ≃ₗ[ZMod 2] Space 3) (b : (V ⧸ W) ≃ₗ[ZMod 2] Space 2)
    (g : parabolic W) :
    quotientTwoCoreEquivThreeTwo W a b (QuotientGroup.mk' _ g) =
      (linearThreeEquivProjective (linearGroupCongr a (subspaceAction W g)),
       linearTwoEquivSymmetricThree (linearGroupCongr b (quotientAction W g))) := rfl

end BinaryLinear.SmallParabolicLevi

end
