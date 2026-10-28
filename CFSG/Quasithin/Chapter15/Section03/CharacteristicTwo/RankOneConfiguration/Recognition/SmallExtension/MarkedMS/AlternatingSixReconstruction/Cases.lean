module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Setup

/-!+# The two remaining whole-core reconstruction branches

The center calculation in `Setup` makes these branches exhaustive. The natural
branch requires the actual action on U/C_U(L), and permits a central fixed
layer in U. In particular it does not force |U|=16: the augmentation cover of
order 32 must remain possible. The exceptional branch keeps irreducibility,
the whole-core order 64, and its exact centralizer.

These are unproved source inputs, not classification theorems. Their independent
producers must establish them from the original MS hypotheses before the
assembly in `Source` proves the requested reconstruction.
Source: Aschbacher--Smith C.1.32(2),(4), pp.135--136; MS93 Main Theorem (2),(6).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open ChapterC
namespace AlternatingSixReconstruction
universe u

/-- The center-free A₆ branch, including the entire elementary central core
and the actual natural action on its central quotient. -/
def NaturalCoreInput (κ : GroupClass.{u}) : Prop :=
  ∀ (J : Type u) [Group J] [Finite J] (L R : Subgroup J), SmallMSPair κ L R →
    ((L ⧸ centralPreimage (pCore 2 L)) ≃*
      commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))) →
    center (L ⧸ pCore 2 L) = ⊥ →
    IsElementaryAbelian 2 (blockU L) ∧
      blockU L ≤ centralizer (pCore 2 L : Set L) ∧
      IsLinearBlockModel L ((BinaryPermutation.naturalRepresentation (Fin 6)).comp
        (alternatingGroup (Fin 6)).subtype)

/-- The exceptional triple-cover branch. The order-three center is supplied
by the proved group-theoretic split, not inferred from a family label. -/
def ExceptionalCoreInput (κ : GroupClass.{u}) : Prop :=
  ∀ (J : Type u) [Group J] [Finite J] (L R : Subgroup J), SmallMSPair κ L R →
    ((L ⧸ centralPreimage (pCore 2 L)) ≃*
      commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))) →
    Nat.card (center (L ⧸ pCore 2 L)) = 3 →
    IsElementaryAbelian 2 (blockU L) ∧
      blockU L ≤ centralizer (pCore 2 L : Set L) ∧
      BlockModuleIrreducible L ∧ Nat.card (blockU L) = 2 ^ 6 ∧
      centralizer (blockU L : Set L) = pCore 2 L

end AlternatingSixReconstruction
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
