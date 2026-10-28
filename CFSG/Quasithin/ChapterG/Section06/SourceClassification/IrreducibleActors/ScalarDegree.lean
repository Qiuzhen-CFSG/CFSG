module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Defining-field lower bound for nonzero binary displacement

Restriction of scalars multiplies every nonzero displacement rank by the
binary degree of the field. In particular, a field-linear action containing
a binary transvection has defining field F2. This supplies the linear and
symplectic row exclusions in the source proof of G.6.4 used by C.5.12.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterG.Section06
open ChapterB.QuasisimpleSource

private theorem binaryField_finrank (F : BinaryField) :
    Module.finrank (ZMod 2) F.Carrier = F.degree := by
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  calc
    2 ^ Module.finrank (ZMod 2) F.Carrier = Nat.card F.Carrier := by
      simpa using (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.Carrier)).symm
    _ = _ := F.card_eq

theorem scalar_degree_le_displacement (F : BinaryField)
    {H W : Type*} [Group H] [AddCommGroup W]
    [Module F.Carrier W] [Module (ZMod 2) W] [IsScalarTower (ZMod 2) F.Carrier W]
    [FiniteDimensional F.Carrier W]
    (τ : Representation F.Carrier H W) (a : H) (hne : τ a ≠ 1) :
    F.degree ≤ Module.finrank (ZMod 2)
      (LinearMap.range ((restrictScalars (k := ZMod 2) τ) a - LinearMap.id)) := by
  let T := τ a - 1
  have hT : T ≠ 0 := by exact fun hz => hne (sub_eq_zero.mp hz)
  have hR : LinearMap.range T ≠ ⊥ := fun hz => hT (LinearMap.range_eq_bot.mp hz)
  have hd : 0 < Module.finrank F.Carrier (LinearMap.range T) :=
    Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hR)
  have he : (restrictScalars (k := ZMod 2) τ) a - LinearMap.id =
      T.restrictScalars (ZMod 2) := rfl
  rw [he, LinearMap.range_restrictScalars]
  change F.degree ≤ Module.finrank (ZMod 2) (LinearMap.range T)
  rw [← Module.finrank_mul_finrank (ZMod 2) F.Carrier, binaryField_finrank]
  exact Nat.le_mul_of_pos_right _ hd
end CFSG.Quasithin.ChapterG.Section06
