module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalOpposition
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.SourceNormalizer

/-!
# Source construction of the marked Ree Weyl-data input

The source root-group representatives are corrected inside their rank-one
groups to involutions. Opposition proves their literal eighth-power relation.
Thus the presentation owner's WeylData receives actual representatives with
proved squares, placement, and mixed relation. Only the two field-unit action
equations remain explicit here, together with the unfinished source charts
and torus construction; these remain this source family's obligations.

The original full-Borel marking discharges the faithful core, and either
endpoint orientation is retained. This includes m=0 and does not identify
any TYPE-only data with an actual marked source quotient.

Source: Fong--Seitz I (6H), p.51, and II (10.42)--(10.43), p.232.
-/

@[expose] public noncomputable section
open Subgroup
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open ReeF4.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
    (Q : MarkedQuotient P) (split : SplitData Q.tits) (s : ∀ i, RootReflection Q split i)

/-- Involutory source representatives with the presentation's original orientation. -/
def sourceWeylLift (orientation b : Bool) : Q.tits.N :=
  (involutoryRootReflection Q split (SourceNormalizer.index orientation b)
    (s (SourceNormalizer.index orientation b))).val

theorem sourceWeylLift_square (orientation b : Bool) :
    sourceWeylLift Q split s orientation b ^ 2 = 1 :=
  Subtype.ext (involutoryRootReflection_sq Q split _ _)

theorem sourceWeylLift_placement (orientation b : Bool) :
    QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N)
      (sourceWeylLift Q split s orientation b) = Q.simple (SourceNormalizer.index orientation b) :=
  (involutoryRootReflection Q split _ _).class_eq

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure (rootAt)
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 8) (n : ℕ) (hn : Odd n) (m : ℕ)
  (μ₀ : (parabolic L S 0 ⧸ originalPanelKernel (L := L) (S := S) 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hB₀ : (originalFaithfulBorel (L := L) (S := S) 0).map μ₀.toMonoidHom = normalizer (T : Set _))
  (μ₁ : (parabolic L S 1 ⧸ originalPanelKernel (L := L) (S := S) 1) ≃* SuzukiMatrixGroup m)
  (hB₁ : (originalFaithfulBorel (L := L) (S := S) 1).map μ₁.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
  (s : ∀ i, RootReflection Q split i)


open ReeF4.RootPresentationRecognition

/-- Instantiate the presentation owner's literal Weyl input. The mixed
relation is proved from source Cartan actions, not supplied by a callback. -/
def originalReeWeylData (d : SourcePositive.Charts Q split m)
    (C : SourceBorel.TorusData Q split d)
    (hact : ∀ b (a : (ReeF4.CoefficientField m)ˣ × (ReeF4.CoefficientField m)ˣ),
      (sourceWeylLift Q split s d.orientation b : X ⧸ Q.D) * C.h a *
        (sourceWeylLift Q split s d.orientation b : X ⧸ Q.D)⁻¹ =
        C.h (NormalizerTables.table m b a)) : SourceNormalizer.WeylData Q split d C := by
  apply SourceNormalizer.WeylData.ofFieldRelations Q split d C
    (sourceWeylLift Q split s d.orientation)
    (sourceWeylLift_square Q split s d.orientation) ?_
    (sourceWeylLift_placement Q split s d.orientation) hact
  let r (i : Fin 2) := (involutoryRootReflection Q split i (s i)).val
  have hinv (i : Fin 2) : (r i)⁻¹ = r i :=
    inv_eq_of_mul_eq_one_right (by
      have hs : r i ^ 2 = 1 := Subtype.ext (involutoryRootReflection_sq Q split i (s i))
      simpa only [pow_two] using hs)
  have hrel : (r 0*r 1)^8 = 1 :=
    original_ree_reflection_product_eight Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁ s
      (r 0) (r 1) (involutoryRootReflection Q split 0 (s 0)).class_eq
      (involutoryRootReflection Q split 1 (s 1)).class_eq
  have hrev : (r 1*r 0)^8 = 1 := by
    have he : r 1*r 0 = (r 0*r 1)⁻¹ := by rw [mul_inv_rev,hinv,hinv]
    rw [he,inv_pow,hrel,inv_one]
  have hmix (o : Bool) :
      (sourceWeylLift Q split s o false * sourceWeylLift Q split s o true)^8 = 1 := by
    cases o
    · exact hrel
    · exact hrev
  exact hmix d.orientation

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
