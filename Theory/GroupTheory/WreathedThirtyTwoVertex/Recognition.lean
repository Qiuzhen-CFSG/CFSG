module
public import Theory.GroupTheory.WreathedThirtyTwoVertex.Presentation
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.WreathedSylow
public import Theory.AtlasPort.LinearGroups.G2.BinarySmallLocals
public import ABG.ChapterII.Section1.WreathedRegularModel

/-!
# Recognizing the actual nonabelian parabolic of G₂(2)′

The intrinsic core, self-centralization and wreathed Sylow facts of the actual
binary octonion commutator satisfy the same order-96 vertex characterization.
Whole-group uniqueness therefore identifies every source vertex with this
literal parabolic. No quotient-model or action-coordinate premise is needed.

Source: Aschbacher–Smith F.1.12(I)(8). The target is the actual first parabolic
of the derived ATLAS G₂(2) model, with its existing subgroup carrier.
-/
@[expose] public section

noncomputable section
open Subgroup Atlas.G2.BinaryParabolicPair
namespace WreathedVertex
variable {G:Type*} [Group G] [Finite G]

private theorem noncommutative_of_model {A:Type*} [Group A] (e:A≃*QuaternionCyclic.Model) :
    ¬IsMulCommutative A := by
  intro hh
  apply model_not_commutative
  exact IsMulCommutative.of_comm (fun a b=>e.symm.injective (by
    rw [map_mul,map_mul];exact hh.is_comm.comm _ _))

theorem equiv_derivedFirst_of_card96 (hG:Nat.card G=96)
    (hc:centralizer (pCore 2 G:Set G)≤pCore 2 G) (hna:¬IsMulCommutative (pCore 2 G))
    (S:Sylow 2 G) (eS:S≃*W) : Nonempty (G≃*derivedFirst) := by
  have hn:¬IsMulCommutative (pCore 2 derivedFirst):=
    noncommutative_of_model derivedIntrinsicCoreEquiv
  obtain ⟨w⟩:=derivedSylow_isWreathedOfHeight.nonempty_mulEquiv_regularWreath
  let t:derivedFirstSylow≃*derivedSylow:=subgroupOfEquivOfLe derivedSylow_le_first
  exact equiv_of_card96 hG card_derivedFirst hc derivedFirst_centralizer_pCore hna hn
    S derivedFirstSylow eS (t.trans w)
end WreathedVertex
