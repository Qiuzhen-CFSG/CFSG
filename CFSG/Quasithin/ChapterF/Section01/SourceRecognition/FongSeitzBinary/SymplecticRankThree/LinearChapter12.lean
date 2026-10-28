module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SymplecticRankThree.LinearGeometry
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SymplecticRankThree.Chapter12

/-!
# Original Chapter12 incidence from the actual linear local quotients

The original preparation supplies F.1.1. The paired local PSL₂ markings
and actual root cardinalities now discharge the (2B)/(3G) radical-normality
premises on the same marked quotient. Together with the selected (6A)(a)
commutator clause, the resulting action satisfies the full proved
projective incidence conclusion. Every finite field of characteristic two
is included. No normality, coset fixation or subdegree is assumed here.

The original local markings and row still belong to their earlier source
producer. For fields larger than F₂, coordinatization, alternating-polarity
realization and symplectic recognition remain with this theorem family.
Source: Fong–Seitz I (2B), (3G), (6A)(a); II (7C), p.193;
Aschbacher–Smith 12.2.2 and F.1.1.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.GroupAction.SymplecticRankThree
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source.FongSeitzBinary
variable {G X F : Type*} [Group G] [Finite G] [Group X]
  [Field F] [Finite F] [CharP F 2]
  {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original Chapter12 geometry with radical normality derived from
the actual paired PSL₂ quotients, preserving the same Q.q. -/
theorem rankOne_c2_linear_source_incidence
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
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0)
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0 ⊓
          ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1)
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1)
        inf_le_left inf_le_right) Q.standardAmalgam) :
    ∃ D : PolarityDesign (C2RankThree.Points Q 1) (Nat.card F),
      (∀ x y, D.incident x y ↔ y = x ∨
        (MulAction.SwappedOrbital.graph (C2RankThree.rightCosetPoint Q 1 1)
          (C2RankThree.neighborPoint Q) (C2RankThree.base_ne_neighbor Q)
          (representative (Q.simple 0) : X ⧸ Q.D)⁻¹
          (C2RankThree.neighbor_swap_base Q) (C2RankThree.neighbor_swap_neighbor Q)).Adj x y) ∧
      D.block (C2RankThree.rightCosetPoint Q 1 1) =
        insert (C2RankThree.rightCosetPoint Q 1 1)
          (MulAction.orbit (MulAction.stabilizer (X ⧸ Q.D) (C2RankThree.rightCosetPoint Q 1 1))
            (C2RankThree.neighborPoint Q)) ∧
      (∀ x y, x ≠ y → (D.line x y).ncard = Nat.card F+1) ∧
      (∀ x y p, x ≠ y → (D.line x y ∩ D.block p).Nonempty) ∧
      (∀ x y z, x ≠ y → z ∉ D.line x y →
        ∃! p, x ∈ D.block p ∧ y ∈ D.block p ∧ z ∈ D.block p) ∧
      (∀ x y z w, z ≠ w → x ≠ z → y ≠ w →
        (D.line x y ∩ D.line z w).Nonempty → (D.line x z ∩ D.line y w).Nonempty) ∧
      (∃ x y z w, x ≠ y ∧ z ∉ D.line x y ∧
        ¬ ∃ p, x ∈ D.block p ∧ y ∈ D.block p ∧ z ∈ D.block p ∧ w ∈ D.block p) := by
  have hf := (D.rankOne_global_local_pair_of_preparation h hmany hn hpsl hH d).1
  exact SymplecticRankThree.marked_projective_incidence_of_linear_row Q e hf split hm μ hq hrow

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
