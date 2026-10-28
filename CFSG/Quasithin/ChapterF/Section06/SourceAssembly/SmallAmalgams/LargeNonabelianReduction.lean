module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.ThirtyTwoRigidity

/-!
# The residual source enumeration has two nonabelian cores and order at least 64

The marked source theorem for an abelian core closes that branch completely.
Its complement has two nonabelian cores, and the original core/center argument
excludes common Sylow orders below 64. The following adapter retains exactly
this genuinely unfinished earlier enumeration; it asserts no universal upper
bound or unproved local model.

Source: Aschbacher--Smith F.1.12(I)(3,12,13) and F.6.5.
-/
@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly
universe u

def LargeNonabelianMarkedAmalgamInput : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (A B : Subgroup G) (S : Sylow 2 G),
    IsGoldschmidtTriple A B → pCore 2 G = ⊥ →
    generalizedFitting A = pCore 2 A → generalizedFitting B = pCore 2 B →
    A ⊓ B = (S : Subgroup G) → 64 ≤ Nat.card S →
    ¬ IsMulCommutative (pCore 2 A) → ¬ IsMulCommutative (pCore 2 B) →
    ExceptionalMarkedAmalgam A B ∨ ExceptionalMarkedAmalgam B A

theorem characteristicTwoMarked_of_large_nonabelian
    (hF1 : LargeNonabelianMarkedAmalgamInput.{u}) :
    CharacteristicTwoMarkedAmalgamInput.{u} := by
  intro G _ _ A B S h hcore hA hB hS hlarge hns
  by_cases ha : IsMulCommutative (pCore 2 A)
  · exact exceptional_marked_of_one_abelian h hcore hA hB S hS hlarge hns (Or.inl ha)
  by_cases hb : IsMulCommutative (pCore 2 B)
  · exact exceptional_marked_of_one_abelian h hcore hA hB S hS hlarge hns (Or.inr hb)
  exact hF1 G A B S h hcore hA hB hS
    (BothNonabelian.common_sylow_card_ge_sixty_four h hcore hA hB S hS hlarge hns ha hb)
    ha hb
end CFSG.Quasithin.ChapterF.SourceAssembly
