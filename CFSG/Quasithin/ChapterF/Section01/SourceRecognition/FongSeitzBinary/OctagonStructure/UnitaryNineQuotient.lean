module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitaryNineQuotient
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.UnitaryNineProper
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.UnitaryNineCenter

/-!
# Excluding a large irreducible section inside the source nine-b subgroup

The proper-subgroup argument first forces the section numerator to equal
X. Its large elementary quotient has kernel of order at most 2^b; the
middle Frattini root lies in the derived subgroup, so it is exactly that
kernel. Coprime centrality then makes the center strictly larger. But the
center's image is an invariant subspace of the irreducible quotient; a
nonzero image would make X abelian. This contradiction excludes the section.

The application uses the literal RootSection action, effective denominator
and projection. Its 2^(8b) size and irreducibility are explicit earlier
representation inputs. The independent projective-degree producer and the
remaining lower-central argument must discharge them in source assembly.
Both orientations, scalar conventions, degree one and the full Borel remain.

Source: Fong--Seitz I (6F), printed p.47, invariant-subgroup exclusion.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
      inf_le_left inf_le_right) Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
include e h split

/-- The source subgroup contains no large irreducible effective section with
full-Cartan-invariant numerator. All subgroup geometry is supplied by the
original factors; the numerical representation input remains explicit. -/
theorem original_linear_unitary_nine_irreducible_section_false
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b))
    (d : RootSection Q split j)
    (hd : d.numerator ≤ unitaryNineSubgroup Q split i j)
    (hH : Q.tits.B ⊓ Q.tits.N ≤ normalizer (d.numerator : Set (X ⧸ Q.D)))
    (hlarge : 2^(8*b) ≤ Nat.card d.EffectiveCarrier)
    (hirr : d.effectiveRepresentation.IsIrreducible) : False := by
  have hn := original_linear_unitary_nine_rootSection_numerator Q e h split hm i j hij
    ha hb hi hj d hd hH hlarge
  have hsource := original_linear_unitary_nine_subgroup Q e h split hm i j hij ha hb hi hj
  have hfixed := (original_linear_unitary_cubic_fixed_roots Q e h split hm i j hij ha hb hi hj).2
  have hab := original_linear_unitary_cubic_radical_abelian Q e h split hm i j hij ha hb hi hj
  exact unitaryNineSubgroup_irreducible_quotient_false Q split hm i j hij hb
    hsource.1 hsource.2.1 hsource.2.2.1 hsource.2.2.2 hab (fun w => (hfixed w).2.1)
    d.numerator hn d.numeratorAction d.effectiveRepresentation hirr
    (QuotientGroup.mk' d.effectiveDenominator) (QuotientGroup.mk'_surjective _)
    (fun _ _ => rfl) hlarge

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
