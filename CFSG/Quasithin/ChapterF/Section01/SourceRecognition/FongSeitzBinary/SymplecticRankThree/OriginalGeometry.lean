module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SymplecticRankThree.SourceGeometry
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SymplecticRankThree.Chapter12

/-!
# C₂ source incidence for the literal Chapter12 preparation

The same original selected-factor preparation used by the full marked
comparison gives F.1.1 and hence faithful primitive action on the finite
marked quotient. The C₂ cell counts and source root commutators discharge
the three suborbits, their sizes, and the kernel bound. Both endpoint
markings still use the supplied Q.q; no map from a universal completion
to the independently generated ambient group is introduced.

The (3G) radical normalities and the selected (6A)(a) row remain explicit
source inputs. Constructing field coordinates, the alternating form and
the normal full symplectic subgroup remains with this source-recognition
family. The imported comparison consumer is conditional on that subgroup;
this incidence theorem does not discharge its model-isomorphism premise.
Source: Fong–Seitz II (7C), p.193; Aschbacher–Smith 12.2.2 and F.1.1.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.GroupAction.SymplecticRankThree
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
include D

/-- The literal Chapter12 preparation supplies local characteristic two;
the source root row now supplies every orbit and kernel premise of the
projective incidence argument on the same marked quotient. -/
theorem rankOne_c2_source_incidence
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {H A B R : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (d : Global.Preparation T L H A B R)
    {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
    {q : ℕ} (hq : 2 ≤ q)
    (hm : rotationOrder Q = 4)
    (hq0 : Nat.card (simpleRoot Q split 0) = q)
    (hq1 : Nat.card (simpleRoot Q split 1) = q)
    (hV : ∀ i, split.U ≤ normalizer (simpleRemainder Q split i : Set (X ⧸ Q.D)))
    (hrow : ⁅simpleRoot Q split 1,C2RankThree.kernelRoot Q split⁆ = ⊥)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0)
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0 ⊓
          ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1)
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1)
        inf_le_left inf_le_right) Q.standardAmalgam) :
    ∃ D : PolarityDesign (C2RankThree.Points Q 1) q,
      (∀ x y, D.incident x y ↔ y = x ∨
        (MulAction.SwappedOrbital.graph (C2RankThree.rightCosetPoint Q 1 1)
          (C2RankThree.neighborPoint Q) (C2RankThree.base_ne_neighbor Q)
          (representative (Q.simple 0) : X ⧸ Q.D)⁻¹
          (C2RankThree.neighbor_swap_base Q) (C2RankThree.neighbor_swap_neighbor Q)).Adj x y) ∧
      D.block (C2RankThree.rightCosetPoint Q 1 1) =
        insert (C2RankThree.rightCosetPoint Q 1 1)
          (MulAction.orbit (MulAction.stabilizer (X ⧸ Q.D) (C2RankThree.rightCosetPoint Q 1 1))
            (C2RankThree.neighborPoint Q)) ∧
      (∀ x y, x ≠ y → (D.line x y).ncard = q+1) ∧
      (∀ x y p, x ≠ y → (D.line x y ∩ D.block p).Nonempty) ∧
      (∀ x y z, x ≠ y → z ∉ D.line x y →
        ∃! p, x ∈ D.block p ∧ y ∈ D.block p ∧ z ∈ D.block p) ∧
      (∀ x y z w, z ≠ w → x ≠ z → y ≠ w →
        (D.line x y ∩ D.line z w).Nonempty → (D.line x z ∩ D.line y w).Nonempty) ∧
      (∃ x y z w, x ≠ y ∧ z ∉ D.line x y ∧
        ¬ ∃ p, x ∈ D.block p ∧ y ∈ D.block p ∧ z ∈ D.block p ∧ w ∈ D.block p) := by
  have hf := (D.rankOne_global_local_pair_of_preparation h hmany hn hpsl hH d).1
  exact SymplecticRankThree.marked_projective_incidence_of_row Q e hf split hq hm hq0 hq1 hV hrow

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
