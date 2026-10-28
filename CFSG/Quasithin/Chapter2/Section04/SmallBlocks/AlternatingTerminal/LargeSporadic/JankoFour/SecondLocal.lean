module
public import CFSG.Quasithin.ChapterC.Section01.LocalCoreDisplacement
public import Theory.GroupTheory.PrimeOrderLift
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Second
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Second.FiveDisplacement

/-!
# The second Janko-four centralizer as an alternating-five escape

A local alternating-five component at a full Sylow moves at most its literal
deleted module of order sixteen in the ambient two-core. The actual second
involution centralizer has an elementary kernel of order 2048, and each
order-five actor moves more than sixteen kernel elements. The faithful map
into the native max1 local model transfers that displacement calculation to
the literal centralizer.

This excludes every alternating-five block from the local C-components of the
second centralizer. Its intersection with the elementary kernel is unrestricted.
The source consumer is Aschbacher--Smith 2.4.25, printed p.543; placement in an
involution centralizer is supplied separately by the original source argument.
-/

public section
namespace CFSG.Quasithin.Chapter2.AlternatingTerminal.JankoFour
open Subgroup Janko4.InvolutionCentralizers.Second
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private noncomputable def ambientToLocal : ambientCentralizer →* Local :=
  localCentralizer.subtype.comp ambientEquivLocal.toMonoidHom

private theorem ambientToLocal_injective : Function.Injective ambientToLocal :=
  localCentralizer.subtype_injective.comp ambientEquivLocal.injective

private theorem ambientKernel_map_toLocal :
    ambientKernel.map ambientToLocal = max1Kernel := by
  rw [ambientKernel_eq_map, map_map]
  have hcomp : ambientToLocal.comp ambientEquivLocal.symm.toMonoidHom =
      localCentralizer.subtype := by
    ext g
    simp only [ambientToLocal, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply]
  rw [hcomp]
  exact map_subgroupOf_eq_of_le max1Kernel_le_localCentralizer

private theorem ambient_five_displacement (x : ambientCentralizer)
    (hx : orderOf x = 5) :
    16 < Nat.card (⁅ambientKernel, zpowers x⁆ : Subgroup ambientCentralizer) := by
  have hg : orderOf (ambientToLocal x) = 5 :=
    (orderOf_injective ambientToLocal ambientToLocal_injective x).trans hx
  have hk : IsPGroup 2 starHom.ker := by
    rw [FiveAction.starHom_ker]
    exact IsPGroup.of_card (n := 11) (Janko4.Cardinality.localKernel_card _ _)
  have ho : orderOf (starHom (ambientToLocal x)) = 5 :=
    (starHom.orderOf_map_eq_of_coprime_of_isPGroup_ker hk _
      (by rw [hg]; decide)).trans hg
  have hc : (⁅ambientKernel, zpowers x⁆ : Subgroup ambientCentralizer).map ambientToLocal =
      ⁅max1Kernel, zpowers (ambientToLocal x)⁆ := by
    rw [map_commutator, ambientKernel_map_toLocal, MonoidHom.map_zpowers]
  have h := FiveAction.sixteen_lt_displacement (ambientToLocal x) ho
  rw [← hc, card_map_of_injective ambientToLocal_injective] at h
  exact h

/-- The literal second centralizer excludes local alternating-five components
at every full Sylow, without assuming a faithful quotient image of the block. -/
theorem second_not_local_alternating_five
    (A : Subgroup ambientCentralizer) (hA : ChapterC.IsAlternatingBlock A 5)
    (S : Sylow 2 ambientCentralizer) : A ∉ ChapterA.Section03.localCComponents S := by
  let := ambientKernel_elementary
  have hle : ambientKernel ≤ pCore 2 ambientCentralizer :=
    le_sSup ⟨inferInstance, IsElementaryAbelian.isPGroup 2 ambientKernel⟩
  exact ChapterC.not_local_alternating_five_of_five_displacement ambientKernel hle
    ambient_five_displacement S A hA

end CFSG.Quasithin.Chapter2.AlternatingTerminal.JankoFour
