module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.MarkedCases
public import CFSG.Quasithin.ChapterF.Section06.Amalgams.WeakBN

/-!
# Exact adapter for the earlier F.1.12 enumeration

The Green Book/Fan/Goldschmidt classification is an earlier source theorem.
This adapter records its exact source-facing input, including the genuine weak
BN hypothesis constructed from the original pair. It does not assert the
classification itself and does not use the legacy unrestricted HypothesisF11.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly
open ChapterF
universe u

/-- The precise earlier F.1.12 enumeration contract for the core-free
characteristic-two branch. -/
def F112MarkedEnumerationInput : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (A B : Subgroup G) (S : Sylow 2 G),
    IsGoldschmidtTriple A B → pCore 2 G = ⊥ →
    generalizedFitting A = pCore 2 A → generalizedFitting B = pCore 2 B →
    A ⊓ B = (S : Subgroup G) → 8 < Nat.card S →
    ¬ Nonempty (S ≃* (Multiplicative (ZMod 2) × DihedralGroup 4)) →
    Source.HypothesisF11 (goldschmidtVertices A B) (A ⊓ B) →
    ExceptionalMarkedAmalgam A B ∨ ExceptionalMarkedAmalgam B A

/-- Once the actual F.1.12 enumeration is supplied, it discharges the
remaining characteristic-two marked input used by the corrected F.6 assembly. -/
theorem characteristicTwoMarked_of_f112
    (hF1 : F112MarkedEnumerationInput.{u}) :
    CharacteristicTwoMarkedAmalgamInput.{u} := by
  intro G _ _ A B S h hcore hA hB hS hlarge hns
  exact hF1 G A B S h hcore hA hB hS hlarge hns
    (h.source_hypothesis_of_characteristic_two hcore hA hB)

end CFSG.Quasithin.ChapterF.SourceAssembly
