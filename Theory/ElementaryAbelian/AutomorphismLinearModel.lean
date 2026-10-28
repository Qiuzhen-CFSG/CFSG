module
public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding

/-!
# Matrix coordinates for elementary abelian automorphism groups

An elementary abelian p-group of order pⁿ has an n-dimensional prime-field
module. Multiplicative automorphisms are precisely its linear automorphisms;
a basis therefore identifies the full automorphism group with GLₙ(p).
The construction returns an actual equivalence, for composing with a given
conjugation action. It generalizes the order-eight construction in
`AutomorphismLinearModelEight` without changing that existing interface.

Source: the elementary abelian/vector-space correspondence used in
Aschbacher–Smith A.1.25, printed p.25.
-/

open scoped IsMulCommutative
@[expose] public section
namespace IsElementaryAbelian
/-- Matrix coordinates on the full automorphism group of an elementary abelian group. -/
noncomputable def mulAutLinearEquivOfCard {p n : ℕ} [Fact p.Prime]
    (E : Type*) [Group E] [Finite E] [IsElementaryAbelian p E]
    (hcard : Nat.card E=p^n) :
    MulAut E ≃* Matrix.GeneralLinearGroup (Fin n) (ZMod p) := by
  classical
  have hdim : Module.finrank (ZMod p) (Additive E)=n := by
    apply Nat.pow_right_injective (Fact.out : p.Prime).one_lt
    have hsize := Module.natCard_eq_pow_finrank (K:=ZMod p) (V:=Additive E)
    change Nat.card E=_ at hsize
    simpa only [Nat.card_zmod,hcard] using hsize.symm
  let autLinear : MulAut E ≃* (Additive E ≃ₗ[ZMod p] Additive E) :=
    { toFun := fun aut =>
        { aut.toAdditive with map_smul' := ZMod.map_smul aut.toAdditive }
      invFun := fun aut => MulEquiv.toAdditive.symm aut.toAddEquiv
      left_inv := by intro aut; ext; rfl
      right_inv := by intro aut; ext; rfl
      map_mul' := by intro aut other; ext; rfl }
  let basis := Module.finBasisOfFinrankEq (ZMod p) (Additive E) hdim
  exact autLinear.trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Additive E)).symm.trans
      (Matrix.GeneralLinearGroup.toLin' basis).symm)
end IsElementaryAbelian

