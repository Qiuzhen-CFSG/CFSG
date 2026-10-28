module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.SourceCharts
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryPresentation.QuotientData
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryPresentation.OriginalComparisons

/-!
# Assembly interface for the U₅ source chart

This file is the narrow assembly boundary between the source-coordinate
calculation and the rank-two presentation.  The record below spells out the
remaining equations in the conventions of `FivePresentation.parameters`; in
particular, the two Hermitian root groups are retained as their full
nonabelian parameter group.  The constructor is deliberately transparent:
the source owner supplies the literal equations and the two marked Weyl
lifts, and the resulting value is the `FiveData` consumed by the existing
quotient and Chapter 12 comparisons.

The chart, field labels and natural-section files do not by themselves prove
these equations.  Keeping this boundary explicit prevents an irreducibility
or an abstract actor profile from being mistaken for a marked presentation.
Source: Fong--Seitz II (8C), pp.202--210.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
open Theory.SpecificGroups.UnitaryFive
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource
open UnitaryPresentation

variable {X E : Type*} [Group X] [Field E] [Finite E] [CharP E 2]
variable {P : Fin 2 → Subgroup X}

/- The exact equation package is useful to both the original and geometric
   consumers.  Its fields are literal equalities in the same quotient, rather
   than model identities in an unrelated carrier. -/
structure Laws (Q : MarkedQuotient P) (split : SplitData Q.tits)
    (i : Fin 2) (J : HermitianForm 5 E) where
  roots : PositiveMaps (X ⧸ Q.D) (Multiplicative E)
    (FivePositive.Parameter J) (Multiplicative E) (FivePositive.Parameter J)
  cartan : (Eˣ × Eˣ) →* (X ⧸ Q.D)
  lifts : MarkedWeyl.Lifts Q i
  equations : (FivePresentation.parameters J).Satisfies
    (Presentation.Generator.ofMaps roots cartan (lifts.s : X ⧸ Q.D)
      (lifts.t : X ⧸ Q.D))
  generate : ReflectionLaws.fullGenerated roots cartan
      (lifts.s : X ⧸ Q.D) (lifts.t : X ⧸ Q.D) = ⊤
  positive_le : roots.generated ≤ split.U
  cartan_le : cartan.range ≤ Q.tits.B ⊓ Q.tits.N

namespace Laws

variable {Q : MarkedQuotient P} {split : SplitData Q.tits}
variable {i : Fin 2} {J : HermitianForm 5 E}

def toData (d : Laws Q split i J) : UnitaryPresentation.FiveData Q split i J :=
  { roots := d.roots
    cartan := d.cartan
    lifts := d.lifts
    equations := d.equations
    generate := d.generate
    positive_le := d.positive_le
    cartan_le := d.cartan_le }

omit [Finite E] in
@[simp] theorem toData_roots (d : Laws Q split i J) : (d.toData).roots = d.roots := rfl
omit [Finite E] in
@[simp] theorem toData_cartan (d : Laws Q split i J) : (d.toData).cartan = d.cartan := rfl
omit [Finite E] in
@[simp] theorem toData_lifts (d : Laws Q split i J) : (d.toData).lifts = d.lifts := rfl

theorem toData_modelHom_surjective
    (κ : E) (hκ : κ + J.conj κ = 1) (hJ : J.form = 1)
    (d : Laws Q split i J) :
    Function.Surjective (d.toData.modelHom J κ hκ hJ) := by
  exact FiveData.modelHom_surjective J κ hκ hJ d.toData

theorem toData_modelHom_generator
    (κ : E) (hκ : κ + J.conj κ = 1) (hJ : J.form = 1)
    (d : Laws Q split i J) (j) :
    d.toData.modelHom J κ hκ hJ
        (FivePresentation.modelGenerators J κ hκ hJ j) =
      Presentation.Generator.ofMaps d.roots d.cartan
        (d.lifts.s : X ⧸ Q.D) (d.lifts.t : X ⧸ Q.D) j := by
  exact FiveData.modelHom_generator J κ hκ hJ d.toData j

theorem toData_modelHom_borel_le
    (κ : E) (hκ : κ + J.conj κ = 1) (hJ : J.form = 1)
    (d : Laws Q split i J) :
    (FivePositive.roots J κ hκ hJ).borel
        (FiveWeyl.h J κ hκ hJ) ≤
      Q.tits.B.comap (d.toData.modelHom J κ hκ hJ) := by
  exact FiveData.modelHom_borel_le J κ hκ hJ d.toData

end Laws

/- The source-coordinate output is packaged without changing its hypotheses.
   This is the only place where the chart owner has to provide the six
   finite equation schemes, the full torus and the marked lifts. -/
def assemble
    (Q : MarkedQuotient P) (split : SplitData Q.tits)
    (i : Fin 2) (J : HermitianForm 5 E)
    (d : Laws Q split i J) : UnitaryPresentation.FiveData Q split i J :=
  d.toData

/- A literal original consumer.  This keeps the source quotient, both endpoint
   maps and the center-kernel argument in the existing `FiveOriginal` API. -/
def original_comparison
    {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (hlocal : HypothesisF11 L S)
    (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (hm : rotationOrder Q = 4)
    (J : HermitianForm 5 E) (κ : E) (hκ : κ + J.conj κ = 1)
    (hJ : J.form = 1) (i : Fin 2) (d : Laws Q split i J) :
    RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
        inf_le_left inf_le_right)
      (MarkedAmalgam.flag (lineParabolic J) (planeParabolic J) i) := by
  exact FiveOriginal.comparison Q (originalMarkedIso Q) hlocal split hm J κ hκ hJ
    (d.toData)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource
