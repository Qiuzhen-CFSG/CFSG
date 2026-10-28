module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SymplecticRankThree.SourceCoordinates
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# Chapter12 comparison after source polar coordinatization

The original local PSL₂ quotients, the selected (6A)(a) commutator and the
actual root orders supply the faithful rank-three action and its kernel.
An orthogonality-preserving point coordinate equivalence now constructs the
normal full symplectic subgroup. Root-normal-generation makes it the whole
quotient, and the saved marking theorem supplies the full Borel, both
endpoints and both squares using the same Q.q, in either permitted orientation.

Polar coordinatization remains an explicit, unproved source obligation.
This adapter discharges the old normal-subgroup/model-equivalence premise;
it does not discharge coordinatization or the earlier producer row inputs.
Source: Higman (1964), Theorem 2(i); Fong–Seitz II (7C), p.193 and (8A), p.197;
Aschbacher–Smith 12.2.2 and F.1.1–12.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {F : Type} [Field F] [Finite F] [CharP F 2]
  {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
include D

/-- The literal symplectic comparison, with geometric coordinates still to be constructed. -/
theorem rankOne_c2_rankThree_comparison_of_polar_coordinates
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {H A B R : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (d : Global.Preparation T L H A B R)
    {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
    (hm : rotationOrder Q = 4)
    (μ : ∀ i, HexagonStructure.localGroup Q split i ≃* PSL(2,F))
    (hq : ∀ i, Nat.card (simpleRoot Q split i) = Nat.card F)
    (hrow : ⁅simpleRoot Q split 1,C2RankThree.kernelRoot Q split⁆ = ⊥)
    (hgen : split.unipotentClosure = ⊤)
    (C : C2RankThree.Points Q 1 ≃ ProjectivePoint F)
    (hC : ∀ x y, Orthogonal (C x) (C y) ↔ y = x ∨
      (MulAction.SwappedOrbital.graph (C2RankThree.rightCosetPoint Q 1 1)
        (C2RankThree.neighborPoint Q) (C2RankThree.base_ne_neighbor Q)
        (representative (Q.simple 0) : X ⧸ Q.D)⁻¹
        (C2RankThree.neighbor_swap_base Q) (C2RankThree.neighbor_swap_neighbor Q)).Adj x y)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0)
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0 ⊓
          ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1)
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1)
        inf_le_left inf_le_right) Q.standardAmalgam) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  have hf := (D.rankOne_global_local_pair_of_preparation h hmany hn hpsl hH d).1
  let := Fintype.ofFinite F
  obtain ⟨m,_,hF⟩ := FiniteField.card F 2
  exact Global.ConcreteAmalgamComparison.symplectic F m m.property
    (by simpa only [Nat.card_eq_fintype_card] using hF)
    (SymplecticRankThree.comparison_of_polar_coordinates Q e hf split hm μ hq hrow hgen C hC)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
