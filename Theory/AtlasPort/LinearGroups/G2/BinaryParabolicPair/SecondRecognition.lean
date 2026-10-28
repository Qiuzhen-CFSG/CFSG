module
public import Theory.GroupTheory.C4SquareSymmetricThreeRecognition
public import Theory.AtlasPort.LinearGroups.G2.ExceptionalLocalQuotients
public import Theory.AtlasPort.LinearGroups.G2.BinarySmallLocals
public import Theory.GroupTheory.OddInvolutionEndpointModels
/-!
# Recognizing the actual abelian-core G₂(2)′ parabolic

The actual second parabolic has its checked C₄-square core, symmetric-three
quotient, order 96 and self-centralizing core. The intrinsic uniqueness
theorem therefore identifies every group with these local properties with
this specific embedded octonion-model parabolic.

Source: Aschbacher–Smith F.1.12(I)(8), printed p.263.
-/
public section
open Subgroup Theory.GroupTheory
namespace Atlas.G2.BinaryParabolicPair
open ExceptionalLocalQuotients
/-- Whole-group recognition with the literal normal kernel and quotient. -/
theorem equiv_derivedSecond_of_c4_square
    {G : Type*} [Group G] [Finite G] (Q : Subgroup G) [Q.Normal]
    (e : Q ≃* C4Square) (hc : Nat.card G=96)
    (hQ : centralizer (Q : Set G) ≤ Q)
    (eq : G ⧸ Q ≃* Equiv.Perm (Fin 3)) : Nonempty (G ≃* derivedSecond) := by
  let er := (derivedSecondQuotientEquiv.trans dihedralEquivPSL.symm).trans
    nonempty_dihedralThreeEquivPerm.some
  have hR : Nat.card (pCore 2 derivedSecond)=16 := by
    rw [Nat.card_congr derivedSecondCoreEquiv.toEquiv,Nat.card_eq_fintype_card]
    decide
  have hd : Nat.card derivedSecond=96 := by
    have hh := (pCore 2 derivedSecond).card_mul_index
    rw [Subgroup.index_eq_card, Nat.card_congr er.toEquiv,hR] at hh
    simpa [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial] using hh.symm
  exact C4SquareExtension.equiv_of_selfCentralizing_c4_square Q (pCore 2 derivedSecond)
    e derivedSecondCoreEquiv hc hd hQ derivedSecond_centralizer_pCore eq er
end Atlas.G2.BinaryParabolicPair
