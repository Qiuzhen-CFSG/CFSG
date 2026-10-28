module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SymplecticRankThree.SourceProjective
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# Chapter12 comparison after ordinary projective coordinatization

The null-polarity realization removes the orthogonality formula previously
required of source coordinates. Ordinary line coordinates on the same
parabolic cosets now suffice, and they are needed only when the field has
more than two elements. The binary branch uses the proved full Sp₄(2)
recognition and field transport. The comparison retains the full Borel,
both endpoint markings, both squares for Q.q and both orientations.

Constructing the ordinary coordinates remains an explicit source obligation;
this is a reduction of that obligation, not the original recognition theorem.
The preceding row, local-marking and normal-generation inputs retain their
existing producers. Source: Higman (1964), Theorem 2(i); Fong–Seitz II (7C)
and (8A); Aschbacher–Smith 12.2.2 and F.1.1–12.
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

/-- The literal symplectic comparison, with only ordinary projective coordinates still explicit. -/
theorem rankOne_c2_rankThree_comparison_of_projective_coordinates
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
    (coordinates : Nat.card F ≠ 2 → ∃ C : C2RankThree.Points Q 1 ≃ ProjectivePoint F,
      ∀ x y z, (C z).submodule ≤ (C x).submodule ⊔ (C y).submodule ↔
        z ∈ SymplecticRankThree.orbitalLine Q x y)
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
    (SymplecticRankThree.comparison_of_projective_coordinates Q e hf split hm μ hq hrow hgen coordinates)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
