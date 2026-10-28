module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryPresentation.ReducedComparisons
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.UnitaryFourChapter12
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.UnitaryFiveChapter12

/-!
# The unitary presentations at the literal Chapter12 consumer

Explicit equations on the same marked finite quotient now construct the
unitary model comparison, retaining both orientations and the whole overlap.
For U₅ the general-q reduced comparison feeds the existing original-extension
restoration and quasithin sieve, producing ConcreteAmalgamComparison for every
selected perfect R; no q=4 or whole-residual premise is added. For U₄ we supply
the ordinary original comparison and the reduced marking used by the independent
outer-extension owner. Its degree-two possibility is retained by restoration.
The residual U₅ application also feeds the existing GlobalExit consumer.

Field reconstruction, the input equations, generation and exhaustive row
selection remain with the source-recognition owners. This module proves the
conditional presentation branch, not the unconditional DGS classification.
Source: DGS, Groups and Graphs, Theorem D, p.224 and (15.2), pp.226–228;
Aschbacher–Smith F.1.12, pp.263–264, and 12.2.2, p.795.
-/
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source.FongSeitzBinary
open ChapterF.Source.FongSeitzBinary.UnitaryPresentation
open ChapterF.Source.DGS85.OriginalExtension
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  {A B R : Subgroup G} (d : Global.Preparation T L H A B R)
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P)
  (split : SplitData Q.tits) (hrot : rotationOrder Q=4)

omit [Finite G] in
include hrot in
/-- For an original marked quotient the ordinary U₄ entry is constructed
from its equations. Both orientations and m=1 are retained. -/
theorem rankOne_unitaryFour_presentation_comparison
    (m : ℕ) (hm : 1≤m) (point : Bool)
    (roots : FourData Q split (if point then 0 else 1)
      (ChapterF.GreenBook.LieModels.UnitaryFour.fieldConj m)
      (ChapterF.GreenBook.LieModels.UnitaryFour.fieldConj_involutive m hm))
    (e : Iso (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  apply Global.ConcreteAmalgamComparison.unitary m hm
  cases point
  · exact Or.inr ⟨e.trans (FourModel.reverseComparison m hm Q split hrot roots)⟩
  · exact Or.inl ⟨e.trans (FourModel.forwardComparison m hm Q split hrot roots)⟩

include D h hmany hn hpsl hH d hrot in
/-- The independent U₄ extension producer receives the actual reduced mark,
not an assumed original-model comparison. Its outer part of S is preserved. -/
theorem rankOne_original_marking_of_unitaryFour_presentation
    (m : ℕ) (hm : 1≤m) (hmgt : 1<m) (point : Bool)
    (roots : FourData Q split (if point then 0 else 1)
      (ChapterF.GreenBook.LieModels.UnitaryFour.fieldConj m)
      (ChapterF.GreenBook.LieModels.UnitaryFour.fieldConj_involutive m hm))
    (e : Iso (reducedAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam) :
    Nonempty (Global.OriginalUnitaryFour.Marking m hm point L R (Global.sourceS L H)) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2
  exact exists_original_unitaryFour_marking_of_reduced_iso hf m hm hmgt point
    (fourReducedComparison Q e split hrot m hm point roots)

include D h hmany hn hpsl hH d hrot in
/-- The source diagram-layer consumer uses that same constructed U₄ marking,
with every original normalized-Borel and selected-factor hypothesis retained. -/
theorem rankOne_not_unitaryFour_presentation_of_layer
    (hp : Group.IsPerfect R) (m : ℕ) (hm : 1≤m) (hmgt : 1<m) (point : Bool)
    (roots : FourData Q split (if point then 0 else 1)
      (ChapterF.GreenBook.LieModels.UnitaryFour.fieldConj m)
      (ChapterF.GreenBook.LieModels.UnitaryFour.fieldConj_involutive m hm))
    (e : Iso (reducedAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hl : Global.NoncentralCoreLayer (((residual H).pCoreIn 2).subgroupOf R)) : False :=
  D.rankOne_global_not_reduced_unitaryFour_of_layer h hmany hn hpsl hH d hp m hm hmgt point
    (fourReducedComparison Q e split hrot m hm point roots) hN hl

include D h hmany hn hpsl hH d hrot in
/-- The general-q U₅ presentation discharges the reduced comparison premise
of the original selected-perfect-R catalogue consumer. -/
theorem rankOne_unitaryFive_presentation_comparison
    (hp : Group.IsPerfect R) {q : ℕ} (hq : IsPrimePow q) (heven : Even q)
    (M : ChapterF.GreenBook.UnitaryFive.Model q)
    (κ : M.F) (hκ : κ+M.form.conj κ=1) (line : Bool)
    (roots : FiveData Q split (if line then 0 else 1) M.form)
    (e : Iso (reducedAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2
  exact D.rankOne_global_comparison_of_reduced_unitaryFive h hmany hn hpsl hH d hp hq heven M line
    (fiveReducedComparison hf Q e split hrot M κ hκ line roots)

include D h hmany hn hpsl hH hrot in
/-- With R already the residual, the same equations and markings feed the
completed original U₅ restoration and prepared completion. -/
theorem rankOne_globalExit_of_unitaryFive_presentation
    {A B : Subgroup G} (d₀ : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) {q : ℕ} (hq : IsPrimePow q) (heven : Even q)
    (M : ChapterF.GreenBook.UnitaryFive.Model q)
    (κ : M.F) (hκ : κ+M.form.conj κ=1) (line : Bool)
    (roots : FiveData Q split (if line then 0 else 1) M.form)
    (e : Iso (reducedAmalgam ![L,residual H] (Global.sourceS L H)) Q.standardAmalgam) :
    RankOneModule.GlobalExit G := by
  have hf := d₀.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2
  exact D.rankOne_globalExit_of_reduced_unitaryFive h hmany hn hpsl hH d₀ hp hq heven M line
    (fiveReducedComparison hf Q e split hrot M κ hκ line roots)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
