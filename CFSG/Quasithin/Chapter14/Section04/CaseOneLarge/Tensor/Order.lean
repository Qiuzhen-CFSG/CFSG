module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Tensor.Actor

/-!
# The order obstruction for the original tensor closure

The actual tensor coordinates identify U/Z(U) with a binary space of
dimension eight. Extraspeciality supplies a center of order two, hence
|U| = 512. Its proved inclusion in the original Sylow subgroup gives
|T| ≥ 512, the obstruction needed by the deleted-tensor amalgam consumer.
No equality between U and O₂(H) is assumed.

Source: Aschbacher--Smith, 14.4.2(5) and 14.4.10(3), printed pp.1006,1011.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative TensorProduct
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.Tensor
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : Subgroup Five} {hAD : AltFive ≤ D}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- Either genuine tensor constituent forces the original closure to have order 512. -/
theorem source_tensor_closure_card (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U) :
    Nat.card F.U = 512 := by
  let := chosen.elementary
  let h := source_closure_geometry F d earlier hq chosen structural alternatives hne
  let : IsElementaryAbelian 2 F.Uhat :=
    F.uhat_elementary_of_point (by decide) h.two h.frattini_point
  have hd : finrank (ZMod 2) (Additive F.Uhat) = 8 := by
    rw [(TensorGeometry.linearCoordinates c).finrank_eq,
      Module.finrank_tensorProduct, BinaryPermutation.finrank_core,
      Fintype.card_fin, c.constituent_model.finrank_four]
  have hcenter :=
    (source_extraspecial_order d earlier hq chosen structural alternatives F hne hZ).1.center_order_p
  have hquot := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat)
  rw [Nat.card_zmod, hd] at hquot
  rw [card_eq_card_quotient_mul_card_subgroup (center F.U), hcenter]
  change Nat.card (Additive F.Uhat) * 2 = 512
  norm_num only [hquot]

/-- The original Sylow subgroup contains the order-512 closure. -/
theorem source_tensor_sylow_card_lower_bound (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U) :
    512 ≤ Nat.card T := by
  rw [← source_tensor_closure_card d earlier hq chosen structural alternatives F hne hZ c]
  exact Nat.card_le_card_of_injective _
    (inclusion_injective (source_closure_le_sylow d earlier hq chosen structural alternatives F))

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
