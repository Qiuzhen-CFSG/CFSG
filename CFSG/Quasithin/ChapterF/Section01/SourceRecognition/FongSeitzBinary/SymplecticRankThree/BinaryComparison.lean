module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.C2RankThree.BinaryRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SymplecticRankThree.Comparison

/-!
# The full binary C₂ comparison for original source markings

The order-two source roots and exact (6A)(a) commutator give a proved
isomorphism from the actual marked quotient to full Sp₄(F₂). Local
characteristic two comes from the original endpoint marking and F.1.1.
The existing Sylow adjustment recovers the full Borel and both standard
parabolics together. Restriction and composition yield both inclusion
squares, with either orientation allowed. No recognition premise remains
in this binary branch; selection of the original row retains its producer.

Source: Fong–Seitz II (7C), p.193, and (8A), p.197;
Aschbacher–Smith F.1.1–12, pp.259–264.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.SymplecticRankThree
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

include e h in
/-- Both original endpoints and their full overlap are recognized over F₂. -/
theorem binary_comparison
    (hm : rotationOrder Q = 4)
    (hq : ∀ i, Nat.card (simpleRoot Q split i) = 2)
    (hrow : ⁅simpleRoot Q split 1,C2RankThree.kernelRoot Q split⁆ = ⊥) :
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      (GreenBook.LieModels.SymplecticFour.amalgam (ZMod 2))) ∨
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      (GreenBook.LieModels.SymplecticFour.amalgam (ZMod 2)).reverse) := by
  have hc := MarkedLocal.parabolic_core_selfCentralizing Q e h
  obtain ⟨E⟩ := C2RankThree.binary_symplectic_equiv Q split (hc 1) hm hq hrow
  rcases C2RankThree.marked_comparison_of_equiv Q split hc E with hf | hf
  · obtain ⟨f⟩ := hf
    exact Or.inl ⟨e.trans f⟩
  · obtain ⟨f⟩ := hf
    exact Or.inr ⟨e.trans f⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.SymplecticRankThree
