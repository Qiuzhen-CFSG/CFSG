module

public import CFSG.Quasithin.ChapterF.Section06.Basic
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.G2
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.M12
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.M12.Aut

/-!
# The remaining marked F.6.5 source cases

The four large binary amalgams are recorded with their original overlap
inclusions, rather than only their three abstract local group types. The
remaining source implication isolates exactly the both-characteristic-two,
core-free branch after the small and split-sixteen alternatives. It records
the genuine earlier marked-amalgam enumeration still owned by F.1.12/F.6.5;
it does not assert that enumeration or assume any F.6.18 classification output.

Source: Aschbacher–Smith F.6.4–5 and F.1.12(I)(3,8,12,13), pp.262–263,305.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly
open GreenBook
universe u

/-- The four original marked large binary amalgams, in source orientation. -/
def ExceptionalMarkedAmalgam {G : Type u} [Group G] (A B : Subgroup G) : Prop :=
  let α := RankTwoAmalgam.ofSubgroups A (A ⊓ B) B inf_le_left inf_le_right
  ExceptionalModels.G2.IsDerivedAmalgam α ∨
    ExceptionalModels.G2.IsFullAmalgam α ∨
      MathieuTwelve.IsM12Amalgam α ∨ AutMathieuTwelve.IsAutM12Amalgam α

/-- The precise remaining F.6.5 enumeration, before any ambient recognition. -/
def CharacteristicTwoMarkedAmalgamInput : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (A B : Subgroup G) (S : Sylow 2 G),
    IsGoldschmidtTriple A B → pCore 2 G = ⊥ →
    generalizedFitting A = pCore 2 A → generalizedFitting B = pCore 2 B →
    A ⊓ B = (S : Subgroup G) → 8 < Nat.card S →
    ¬ Nonempty (S ≃* (Multiplicative (ZMod 2) × DihedralGroup 4)) →
    ExceptionalMarkedAmalgam A B ∨ ExceptionalMarkedAmalgam B A

end CFSG.Quasithin.ChapterF.SourceAssembly
