module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.NonabelianRadicals
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.MarkedLocal
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RootCoordinates.SourceApplication

/-!+# The first hexagon structural conclusion on the original source

Both radicals of the same finite marked quotient have nontrivial subgroup
commutators. The MarkedLocal application uses the literal common Sylow
map of the original amalgam, so it also applies to the geometric marking
on an infinite universal completion. The SourceQuotient application uses
the original quotient map Q.q on S. Neither changes an endpoint or assumes
a universal-to-ambient descent or perfectness of the original local factors.

Source: Fong--Seitz I (6E), first paragraph of the proof, printed p.44.
The earlier Section 5 choice of a Weyl lift in each root-generated R_i
remains explicit. These are the two nonabelian-radical clauses required
by GTwoSource and also used in the unequal-parameter TrialitySource route;
the catalogue and all other structural clauses remain to be established.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}

/-- The radical as a literal intersection of the original marked Sylow image. -/
theorem marked_radical_eq (h : HypothesisF11 L S) (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam)
    (split : SplitData Q.tits) (i : Fin 2) (n : Q.tits.N)
    (hn : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n = Q.simple i) :
    simpleRemainder Q split i = (MarkedLocal.sylowMap Q e h).range ⊓
      rightConjugate (MarkedLocal.sylowMap Q e h).range (n : X ⧸ Q.D) := by
  rw [MarkedLocal.sylow_range Q e h split, simpleRemainder,
    unipotentConjugate_eq split (Q.simple i) n hn]

/-- Both canonical radicals are nonabelian on the same original or geometric
marked amalgam. The only reflection premise is the earlier source choice in R_i. -/
theorem marked_original_radicals_nonabelian (h : HypothesisF11 L S)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : rotationOrder Q = 6)
    (s : ∀ i, RootReflection Q split i) :
    let U := (MarkedLocal.sylowMap Q e h).range
    ⁅U ⊓ rightConjugate U ((s 0).val : X ⧸ Q.D),
      U ⊓ rightConjugate U ((s 0).val : X ⧸ Q.D)⁆ ≠ ⊥ ∧
    ⁅U ⊓ rightConjugate U ((s 1).val : X ⧸ Q.D),
      U ⊓ rightConjugate U ((s 1).val : X ⧸ Q.D)⁆ ≠ ⊥ := by
  dsimp only
  rw [← marked_radical_eq h Q e split 0 (s 0).val (s 0).class_eq,
    ← marked_radical_eq h Q e split 1 (s 1).val (s 1).class_eq]
  exact both_radical_commutators_ne_bot Q split hm s

/-- The same two conclusions using the literal quotient image of original S. -/
theorem quotient_original_radicals_nonabelian (h : HypothesisF11 L S)
    (Q : SourceQuotient L S) (split : SplitData Q.tits) (hm : rotationOrder Q = 6)
    (s : ∀ i, RootReflection Q split i) :
    let U := (S.subgroupOf (generated L S)).map Q.q
    ⁅U ⊓ rightConjugate U ((s 0).val : (generated L S) ⧸ Q.D),
      U ⊓ rightConjugate U ((s 0).val : (generated L S) ⧸ Q.D)⁆ ≠ ⊥ ∧
    ⁅U ⊓ rightConjugate U ((s 1).val : (generated L S) ⧸ Q.D),
      U ⊓ rightConjugate U ((s 1).val : (generated L S) ⧸ Q.D)⁆ ≠ ⊥ := by
  dsimp only
  rw [quotient_sourceS_image_eq_unipotent h Q split,
    ← unipotentConjugate_eq split (Q.simple 0) (s 0).val (s 0).class_eq,
    ← unipotentConjugate_eq split (Q.simple 1) (s 1).val (s 1).class_eq]
  exact both_radical_commutators_ne_bot Q split hm s

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
