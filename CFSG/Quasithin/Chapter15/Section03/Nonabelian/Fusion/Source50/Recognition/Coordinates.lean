module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Assembly.PlusType
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Inputs

/-!
# Literal natural–dual coordinates after 15.3.58 recognition

The two irreducible constituents share one actor isomorphism: the first is
natural and the polar pairing identifies the second with its contragredient.
Their complementary sum gives equivariant coordinates on the original U/Z.
These are the coordinates required by the later 15.3.59 fusion argument.
Source: Aschbacher–Smith, 15.3.58(3), printed p.1149.
-/

@[expose] public section

open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
open NormalReduction
universe u
variable {G : Type u} [Group G] [Finite G] {Z ZS V M : Subgroup G}
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)] [IsElementaryAbelian 2 V]
  {C : GroupClass.{u}} {v : ActorQuotient Z} {s : ℕ}
  {d : EarlierSourceInputs Z ZS V M C v s} {a : EarlierActionInputs d}

namespace NaturalPair
variable (p : NaturalPair d a)

/-- The dual coordinate map retains the first constituent's group marking. -/
noncomputable def dualCoordinates : Representation.Equiv p.pair.second.toRepresentation
    (BinaryLinearThree.W.dual.comp
      (p.first_model.actor.trans Matrix.PSL3Two.equiv.symm).toMonoidHom) :=
  Classical.choice p.dual_pairing

/-- Sum coordinates on the actual additive quotient U/Z. -/
noncomputable def linearCoordinates : Space Z ZS ≃ₗ[ZMod 2]
    Fusion.Core.ResidualGeneration.NaturalDualSpace :=
  (Submodule.prodEquivOfIsCompl _ _ p.pair.complement).symm.trans
    (p.first_model.space.prodCongr p.dualCoordinates.toLinearEquiv)

omit [Finite G] in
theorem linearCoordinates_symm_apply
    (x : Fusion.Core.ResidualGeneration.NaturalDualSpace) :
    p.linearCoordinates.symm x =
      (p.first_model.space.symm x.1 : Space Z ZS) +
      (p.dualCoordinates.symm x.2 : Space Z ZS) := rfl

omit [Finite G] in
/-- The coordinates intertwine the same actual K* action on both factors. -/
theorem linearCoordinates_equivariant (k : p.K) (w : Space Z ZS) :
    p.linearCoordinates (actorRepresentation Z ZS d.kernel k w) =
      (BinaryLinearThree.W (Matrix.PSL3Two.equiv.symm (p.first_model.actor k))
        (p.linearCoordinates w).1,
       BinaryLinearThree.W.dual (Matrix.PSL3Two.equiv.symm (p.first_model.actor k))
        (p.linearCoordinates w).2) := by
  apply p.linearCoordinates.symm.injective
  rw [p.linearCoordinates.symm_apply_apply, p.linearCoordinates_symm_apply]
  have h₁ (x : BinaryLinearThree.Vector) :
      p.first_model.space.symm
        (BinaryLinearThree.W (Matrix.PSL3Two.equiv.symm (p.first_model.actor k)) x) =
      p.pair.first.toRepresentation k (p.first_model.space.symm x) := by
    apply p.first_model.space.injective
    rw [p.first_model.space.apply_symm_apply, p.first_model.intertwines,
      p.first_model.space.apply_symm_apply]
  have h₂ (x : Module.Dual (ZMod 2) BinaryLinearThree.Vector) :
      p.dualCoordinates.symm
        (BinaryLinearThree.W.dual (Matrix.PSL3Two.equiv.symm (p.first_model.actor k)) x) =
      p.pair.second.toRepresentation k (p.dualCoordinates.symm x) := by
    apply p.dualCoordinates.toEquiv.injective
    change p.dualCoordinates (p.dualCoordinates.symm
      (BinaryLinearThree.W.dual (Matrix.PSL3Two.equiv.symm (p.first_model.actor k)) x)) =
      p.dualCoordinates (p.pair.second.toRepresentation k (p.dualCoordinates.symm x))
    rw [p.dualCoordinates.apply_symm_apply]
    simpa only [LinearMap.comp_apply, Equiv.coe_toLinearMap, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply, p.dualCoordinates.apply_symm_apply] using
      (LinearMap.congr_fun (p.dualCoordinates.isIntertwining' k)
        (p.dualCoordinates.symm x)).symm
  rw [h₁, h₂]
  change actorRepresentation Z ZS d.kernel k w =
    actorRepresentation Z ZS d.kernel k (p.first_model.space.symm
      (p.linearCoordinates w).1 : Space Z ZS) +
    actorRepresentation Z ZS d.kernel k (p.dualCoordinates.symm
      (p.linearCoordinates w).2 : Space Z ZS)
  rw [← map_add, ← p.linearCoordinates_symm_apply,
    p.linearCoordinates.symm_apply_apply]

omit [Finite G] in
/-- The first coordinate subspace is exactly the recognized natural summand. -/
theorem mem_first_iff (w : Space Z ZS) :
    w ∈ p.pair.first.toSubmodule ↔ (p.linearCoordinates w).2 = 0 := by
  change w ∈ p.pair.first.toSubmodule ↔
    p.dualCoordinates.toLinearEquiv
      ((Submodule.prodEquivOfIsCompl _ _ p.pair.complement).symm w).2 = 0
  rw [p.dualCoordinates.toLinearEquiv.map_eq_zero_iff]
  exact (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero _ _
    p.pair.complement).symm

omit [Finite G] in
/-- The second coordinate subspace is exactly the recognized dual summand. -/
theorem mem_second_iff (w : Space Z ZS) :
    w ∈ p.pair.second.toSubmodule ↔ (p.linearCoordinates w).1 = 0 := by
  change w ∈ p.pair.second.toSubmodule ↔
    p.first_model.space
      ((Submodule.prodEquivOfIsCompl _ _ p.pair.complement).symm w).1 = 0
  rw [p.first_model.space.map_eq_zero_iff]
  exact (Submodule.prodEquivOfIsCompl_symm_apply_fst_eq_zero _ _
    p.pair.complement).symm

/-- Multiplicative coordinates use the literal quotient expected by fusion. -/
noncomputable def coordinates : VectorQuotient Z ZS ≃*
    Multiplicative Fusion.Core.ResidualGeneration.NaturalDualSpace :=
  { toFun := fun w => Multiplicative.ofAdd (p.linearCoordinates (Additive.ofMul w))
    invFun := fun w => (p.linearCoordinates.symm w.toAdd).toMul
    left_inv w := congrArg Additive.toMul
      (p.linearCoordinates.symm_apply_apply (Additive.ofMul w))
    right_inv w := congrArg Multiplicative.ofAdd
      (p.linearCoordinates.apply_symm_apply w.toAdd)
    map_mul' w z := p.linearCoordinates.map_add (Additive.ofMul w) (Additive.ofMul z) }

omit [Finite G] in
/-- Source quotient conjugation agrees with the common natural–dual marking. -/
theorem coordinates_equivariant (h : centralizerH Z) (k : p.K)
    (hk : QuotientGroup.mk' (pCore 2 (centralizerH Z)) h = k) (w : VectorQuotient Z ZS) :
    (p.coordinates (quotientAction Z ZS h w)).toAdd =
      (BinaryLinearThree.W (Matrix.PSL3Two.equiv.symm (p.first_model.actor k))
        (p.coordinates w).toAdd.1,
       BinaryLinearThree.W.dual (Matrix.PSL3Two.equiv.symm (p.first_model.actor k))
        (p.coordinates w).toAdd.2) := by
  change p.linearCoordinates (Additive.ofMul (quotientAction Z ZS h w)) = _
  change p.linearCoordinates (Additive.ofMul (quotientAction Z ZS h
    (Additive.ofMul w).toMul)) = _
  rw [← actorRepresentation_mk Z ZS d.kernel, hk]
  exact p.linearCoordinates_equivariant k _

end NaturalPair
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
