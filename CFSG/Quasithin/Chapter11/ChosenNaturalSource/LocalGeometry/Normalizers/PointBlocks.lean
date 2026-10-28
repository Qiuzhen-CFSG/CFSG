module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Conditions
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Orbit

/-!
# Assembly of the nonbinary point-block branches

The genuine flag supplies all MS-pair premises inside LR₁. The remaining
source classification has three marked rows: linear three gives the actual
SL₃ block, symplectic four gives the actual Sp₄(4) block, and nonbinary G₂
is excluded. Once those independent classification implications are supplied,
shortness identifies the chosen seed with U(L), giving V=V_M. The final
consumer passes this exact conjunction to the original radical alternative.

The row implications are pending source proofs, not consequences of this
module. In particular neither a group-family label nor a central-core order
bound supplies their block-model conclusions. The linear row must establish
the point-radical exclusion in C.1.34, and both nonlinear rows include q=4.

Source: Aschbacher--Smith, combined manuscript, C.1.31--34, printed
pp.135--137, and the first paragraph of 11.1.5, printed p.765.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The exact linear point-radical specialization, still requiring its source
proof. The quotient marking includes full SL₃, including its odd center. -/
def LinearPointRecognition : Prop :=
  ∀ m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3),
    ∀ f : InvariantFlag (.sl3 m), NonbinaryMSPair S.field L (f.Ri 0) →
      ChapterC.IsSL3EvenBlock L S.field.degree

/-- The nonbinary symplectic MS row must construct an actual Sp₄(4) block. -/
def SymplecticPointRecognition : Prop :=
  ∀ m : ActionEquiv D.centralQuotientAction
    (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)),
    ∀ f : InvariantFlag (.sp4 m), NonbinaryMSPair S.field L (f.Ri 0) →
      ChapterC.IsSp4FourBlock L

/-- C.1.32 excludes the genuinely marked nonbinary G₂ row. -/
def ExceptionalPointExclusion : Prop :=
  ∀ m : ActionEquiv D.centralQuotientAction
    (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)),
    ∀ f : InvariantFlag (.g2 m), NonbinaryMSPair S.field L (f.Ri 0) → False

/-- Conditional assembly of the first paragraph of 11.1.5. All MS inputs
are discharged here; the three nonbinary classification branches remain. -/
theorem chosen_point_blocks_of_recognition
    (hlinear : LinearPointRecognition D S)
    (hsymplectic : SymplecticPointRecognition D S)
    (hexceptional : ExceptionalPointExclusion D S)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hescape : ¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) :
    V = Source.conjugateSpan (normalizer (L : Set G)) V ∧
      (ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L) := by
  have hm := point_msPair D S f hescape
  apply point_blocks_with_span D
  cases c with
  | sl3 m => exact Or.inl (hlinear m f hm)
  | sp4 m => exact Or.inr (hsymplectic m f hm)
  | g2 m => exact (hexceptional m f hm).elim

/-- The actual RadicalAssembly consumer, with its cohomology and fixed-summand
premises unchanged. This discharges its hblocks callback conditionally on the
three explicitly pending classification implications above. -/
theorem radicalAlternative_of_point_recognition
    (hlinear : LinearPointRecognition D S)
    (hsymplectic : SymplecticPointRecognition D S)
    (hexceptional : ExceptionalPointExclusion D S)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hcenter : (¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) →
      (ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L) →
      radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L)
    (hfixed : (¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) →
      (ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L) →
      radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L →
      normalizer (f.Ri 0 : Set G) ≤ normalizer (radicalFixedCenter (f.Ri 0) L : Set G)) :
    Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree :=
  chosen_radicalAlternative_of_source_steps D S f
    (chosen_point_blocks_of_recognition D S hlinear hsymplectic hexceptional f)
    hcenter hfixed

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks
