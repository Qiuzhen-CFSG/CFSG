module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Normalizers.Images
public import Theory.Representation.PSL3Two.SmallModules
public import Theory.GroupAction.CommonFixedNormalizer

/-!
# Exact recognition input for the residual block model calculation

These data identify the literal actor quotient with `Aut(SL₃(2))` and the
literal vector quotient with the natural module plus its contragredient.
Equivariance is specified on every inner actor, using its actual matrix.
No fixed-space, normalizer or orbit conclusion is a field of this input.

Source: Aschbacher–Smith 15.3.58, combined manuscript (1 March 2004), p.1148.
-/

public section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Normalizers
variable {G : Type*} [Group G]

/-- The actual recognition supplied by 15.3.58, restricted to the action
information consumed by the block argument. -/
structure RecognizedAction (Z ZS : Subgroup G)
    [(Z.subgroupOf (closureU Z ZS)).Normal]
    [IsElementaryAbelian 2 (VectorQuotient Z ZS)]
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z)) where
  actorEquiv : ActorQuotient Z ≃* MulAut BinaryLinearThree.Group
  vectorEquiv : Recognition.Space Z ZS ≃ₗ[ZMod 2]
    (BinaryLinearThree.Vector × Module.Dual (ZMod 2) BinaryLinearThree.Vector)
  inner_equivariant : ∀ (g : BinaryLinearThree.Group) (w : Recognition.Space Z ZS),
    vectorEquiv (Recognition.actorRepresentation Z ZS hkernel
      (actorEquiv.symm (MulAut.conj g)) w) =
      (BinaryLinearThree.W g (vectorEquiv w).1,
        BinaryLinearThree.W.dual g (vectorEquiv w).2)

/-- The intrinsic four-group facts still to be established from the recognized
action. This is a model-calculation contract, not a source assumption or a
proof of the residual block theorem. Its normalizer is in `H*`. -/
@[expose] def FourGroupModelFacts (Z ZS : Subgroup G)
    [(Z.subgroupOf (closureU Z ZS)).Normal]
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z)) : Prop :=
  ∀ A : Subgroup (ActorQuotient Z), A ≤ Recognition.actorImage Z (residualK Z) →
    IsElementaryAbelian 2 A → Nat.card A = 4 →
    Nat.card ((actorAction Z ZS hkernel).commonFixed A) = 8 ∧
    (∀ a : ActorQuotient Z,
      (∀ w ∈ (actorAction Z ZS hkernel).commonFixed A,
        actorAction Z ZS hkernel a w = w) → a ∈ A) ∧
    Nonempty (Subgroup.normalizer (A : Set (ActorQuotient Z)) ≃* Equiv.Perm (Fin 4)) ∧
    Nat.card A.normalizerMonoidHom.range = 6

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Normalizers
