module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.UnitaryNineProper
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SourceSelection.UnitaryNineSubgroupChapter12

/-!
# Chapter 12's proper invariant-subgroup exclusion

The same original factors and full marked quotient give the 2^b index gap
for every proper Cartan-invariant subgroup of the nine-b subgroup. An
actual elementary section of order at least 2^(8b) forces its containing
subgroup to equal the whole nine-b subgroup. The literal RootSection
application keeps its effective denominator and quotient map unchanged.

Source: Fong--Seitz I (6F), printed p.47, applied at AS 12.2.2. The sharp
section bound, whole-subgroup exclusion and lower-central persistence
retain their original source producers and final discharge.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.FongSeitzBinary.OctagonStructure
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
  (split : SplitData Q.tits) (hm : rotationOrder Q=8)
include D h hmany hn d hTH e split hm

/-- The original Chapter 12 factors force the proper-subgroup index gap. -/
theorem rankOne_octagon_unitary_nine_proper_index
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {b : ℕ} (hb : 0 < b)
    (hR : ClassicalGroup.IsPSU (R ⧸ pCore 2 R) 3 (2^b) ∨
      IsSU (R ⧸ pCore 2 R) 3 (2^b)) :
    ∀ W : Subgroup (X ⧸ Q.D), W < unitaryNineSubgroup Q split 0 1 →
      Q.tits.B ⊓ Q.tits.N ≤ normalizer (W : Set (X ⧸ Q.D)) →
      2^b ≤ W.relIndex (unitaryNineSubgroup Q split 0 1) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact original_linear_unitary_nine_proper_index Q e hf split hm 0 1 (by decide)
    (by omega) hb hpsl hR

/-- A large elementary section excludes a proper invariant candidate. -/
theorem rankOne_octagon_unitary_nine_large_section_eq
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {b : ℕ} (hb : 0 < b)
    (hR : ClassicalGroup.IsPSU (R ⧸ pCore 2 R) 3 (2^b) ∨
      IsSU (R ⧸ pCore 2 R) 3 (2^b))
    (W : Subgroup (X ⧸ Q.D)) (hW : W ≤ unitaryNineSubgroup Q split 0 1)
    (hH : Q.tits.B ⊓ Q.tits.N ≤ normalizer (W : Set (X ⧸ Q.D)))
    {Z : Type*} [Group Z] [IsElementaryAbelian 2 Z]
    (A : Subgroup W) (f : A →* Z) (hsurj : Function.Surjective f)
    (hlarge : 2^(8*b) ≤ Nat.card Z) : W=unitaryNineSubgroup Q split 0 1 := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact original_linear_unitary_nine_large_section_eq Q e hf split hm 0 1 (by decide)
    (by omega) hb hpsl hR W hW hH A f hsurj hlarge

/-- The actual effective quotient forces its numerator to be the whole
source subgroup; the degree bound remains an explicit input. -/
theorem rankOne_octagon_unitary_nine_rootSection_numerator
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {b : ℕ} (hb : 0 < b)
    (hR : ClassicalGroup.IsPSU (R ⧸ pCore 2 R) 3 (2^b) ∨
      IsSU (R ⧸ pCore 2 R) 3 (2^b))
    (δ : RootSection Q split 1)
    (hδ : δ.numerator ≤ unitaryNineSubgroup Q split 0 1)
    (hH : Q.tits.B ⊓ Q.tits.N ≤ normalizer (δ.numerator : Set (X ⧸ Q.D)))
    (hlarge : 2^(8*b) ≤ Nat.card δ.EffectiveCarrier) :
    δ.numerator=unitaryNineSubgroup Q split 0 1 := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact original_linear_unitary_nine_rootSection_numerator Q e hf split hm 0 1 (by decide)
    (by omega) hb hpsl hR δ hδ hH hlarge

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
