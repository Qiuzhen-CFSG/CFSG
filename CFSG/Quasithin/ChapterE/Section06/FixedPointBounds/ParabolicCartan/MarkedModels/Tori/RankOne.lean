module

public import BenderSuzuki.Converse.PSL2
public import Theory.SpecificGroups.Suzuki.StandardSubgroups

/-!
# Concrete torus in the marked RankOne Borel

The diagonal torus embeds in the projective linear Borel in characteristic
two, and the actual Suzuki split torus embeds in its named Borel.

These proofs adapt the corresponding `BorelReduction/RankOneTori`
module in Chapter 15, using only the underlying matrix mathematics and no
later source assumptions. Their consumer is `MarkedModels.Cyclic`.
Source: Aschbacher--Smith, E.2.2, printed pp.215--216; the rank-one matrices
are those of Huppert II.10.12 and Huppert--Blackburn XI.3.1--3.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Tori
open Subgroup BenderSuzuki.Converse BenderSuzuki.MatrixGroups

variable {F : Type*} [Field F]

/-- The usual diagonal split torus inside the actual triangular Borel. -/
def sl2Torus : Fˣ →* Borel F :=
  (torHom F).codRestrict _ (fun a => Torus_le_Borel (Torus_eq_range (F := F) ▸ ⟨a, rfl⟩))

theorem sl2Torus_injective : Function.Injective (sl2Torus (F := F)) := by
  intro a b h
  exact torHom_injective (congrArg Subtype.val h)

/-- The image of the diagonal torus in the actual projective Borel. -/
def psl2Torus : Fˣ →* PBorel F :=
  ((pi F).comp (torHom F)).codRestrict _ (by
    intro a
    rw [PBorel_eq_map]
    exact mem_map_of_mem _ (sl2Torus a).property)

theorem psl2Torus_injective [CharP F 2] : Function.Injective (psl2Torus (F := F)) := by
  intro a b h
  exact torHom_injective (pi_injective (congrArg Subtype.val h))

/-- The matrix Suzuki split torus, included in its standard Borel. -/
noncomputable def suzukiTorus (m : ℕ) (hm : 0 < m) :
    (BenderSuzuki.PFAppendixIII.BinaryGaloisField (2 * m + 1))ˣ →* SuzukiBorelSubgroup m :=
  (inclusion (suzukiBorelSubgroup_eq_sup m ▸ le_sup_right)).comp
    (suzukiSplitTorus_equiv_units m hm).some.toMonoidHom

theorem suzukiTorus_injective (m : ℕ) (hm : 0 < m) :
    Function.Injective (suzukiTorus m hm) := by
  exact (inclusion_injective (suzukiBorelSubgroup_eq_sup m ▸ le_sup_right)).comp
    (suzukiSplitTorus_equiv_units m hm).some.injective

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Tori
