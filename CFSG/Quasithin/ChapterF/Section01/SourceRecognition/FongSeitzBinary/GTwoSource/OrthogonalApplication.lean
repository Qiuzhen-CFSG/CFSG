module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.OrthogonalRoots
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.GTwoSource.ReflectionApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.G2Presentation.Recognition

/-!
# Source G₂ applications without a separate orthogonal centralizer input

The same six reflection-aligned source roots now reach the published
positive consumer from PartialPositiveData alone: the two orthogonal
rank-one centralizers are derived from FA and EC commutation and the
hexagon root intersections. Both original endpoint equations and the
literal Q.q specialization are retained, over all characteristic-two
fields including F₂ and F₄.

For F₂, OrthogonalRoots proves the last two fixed-root Weyl equations
directly from the order-two root groups. Together with the checked
BinaryCartan results this constructs the full RootData on the SAME
quotient from the remaining lower positive equations, core-freeness and
source normal generation. Apply the existing G2Presentation.Recognition
consumer: the resulting conditional comparison preserves the full Borel,
original S, both orientations and the full overlap. The native orientation
also reaches the actual null-plane/singular-point geometric amalgam.
The comparison is with full G₂(2), without a simplicity assumption.

This is NOT the source 6E(a) -> 9A theorem. PartialPositiveData still
requires the coupled module/mixed-root construction, including the binary
case; higher fields also need the remaining Cartan and braid equations.
Earlier local-section/kernel, core-free Borel and normal-generation inputs
remain with their source producers and final assembly. No universal-to-
original descent is assumed.

Source: Fong--Seitz I (3G), II (9.5)--(9.6), printed p.212, and (9A),
printed pp.210--217; DGS Theorem D, printed p.224, for the marked comparison.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open Atlas.G2.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.GTwoSource.OrthogonalSource
variable {G X F : Type*} [Group G] [Group X] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (hm : rotationOrder Q = 6)
  (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
  (μ : ∀ i, localGroup Q split i ≃* PSL(2,F))
  (n : ∀ i, RootReflection Q split i) (short : Fin 2)
  (d₀ : PartialPositiveData (alignedSourceRoots Q split hK μ n short))
  (h : HypothesisF11 L S)

include hm d₀ h in
/-- The positive consumer no longer requires separate orthogonal centralization.
Its remaining lower-module equations are exactly the explicit input d₀. -/
theorem positive_marked_application :
    ∃ f : Atlas.G2.unipotent (K := F) →* S, Function.Surjective f ∧
      ∀ (i : Fin 2) (a : Fin 6 → F),
        let s := f (Atlas.G2.unipotentEquiv a)
        MarkedLocal.endpointMap Q e i
          ⟨s, (show S ≤ parabolic L S i from le_sup_right.trans le_sup_left) s.property⟩ =
            (alignedSourceRoots Q split hK μ n short).product a := by
  let hc := aligned_short_centralizes Q split hK μ n short hm d₀.commuting
  exact ⟨ReflectionPositive.sourceSylowHom Q split e hm hK μ n short hc d₀ h,
    ReflectionPositive.sourceSylowHom_surjective Q split e hm hK μ n short hc d₀ h,
    ReflectionPositive.sourceSylowHom_endpoint Q split e hm hK μ n short hc d₀ h⟩

include hm d₀ in
/-- Both missing fixed-root equations follow on the same full-Cartan datum. -/
theorem quotient_fixed_roots (hH : IsMulCommutative ↥(Q.tits.B ⊓ Q.tits.N)) :
    let d := sourceBorelWeyl Q split hK μ n short hH
    (∀ a, d.s*d.x 0 a*d.s⁻¹ = d.x 0 a) ∧
      (∀ a, d.r*d.x 2 a*d.r⁻¹ = d.x 2 a) :=
  ⟨sourceBorelWeyl_sA Q split hK μ n short hH hm d₀.commuting,
    sourceBorelWeyl_rC Q split hK μ n short hH hm d₀.commuting⟩

section Binary
variable (hF : Nat.card F = 2) (hcore : Q.tits.B.normalCore = ⊥)
  (hgen : split.unipotentClosure = ⊤)

/-- Every binary presentation clause is now supplied from the constructed maps
and the remaining lower positive equations. No Relations record is an input. -/
def binaryRootData : RootData Q split F short where
  data := binarySourceBorelWeyl Q split hK μ n short hm hF hcore
  relations := binarySourceBorelWeyl_relations Q split hK μ n short hm hF hcore d₀
  generate := sourceBorelWeyl_whole Q split hK μ n short
    (binaryCartanCommutative Q split hK μ n short hm hF hcore) hm hgen
  positive := alignedSourceRoots_generated Q split hK μ n short hm
  highest_nontrivial := alignedSourceRoots_highest_nontrivial Q split hK μ n short
  short_placement := (sourceReflection_placements Q split n short).1
  long_placement := (sourceReflection_placements Q split n short).2

/-- Apply the already proved full presentation, preserving both orientations. -/
def binaryComparison : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    (flagAmalgam F short) :=
  G2Presentation.comparison Q e split
    (binaryRootData Q split hm hK μ n short d₀ hF hcore hgen)

/-- The constructed equivalence compares the original U, full B, and BOTH
parabolics with the full G₂(2) model, rather than its proper derived subgroup. -/
theorem binary_subgroup_images :
    let f := G2Presentation.quotientEquiv Q split
      (binaryRootData Q split hm hK μ n short d₀ hF hcore hgen)
    split.U.map f.toMonoidHom = Atlas.G2.unipotent ∧
    Q.tits.B.map f.toMonoidHom = Atlas.G2.borel ∧
    (Q.tits.standardParabolic {Q.simple short}).map f.toMonoidHom =
      Atlas.G2.LieParabolicSetup.parabolic₁ ∧
    (Q.tits.standardParabolic {Q.simple (1-short)}).map f.toMonoidHom =
      Atlas.G2.LieParabolicSetup.parabolic₂ :=
  G2Presentation.subgroup_images Q split
    (binaryRootData Q split hm hK μ n short d₀ hF hcore hgen)

theorem binary_comparison_left (a : parabolic L S 0) :
    ((binaryComparison Q split e hm hK μ n short d₀ hF hcore hgen).left a :
      Atlas.G2.Model F) =
      G2Presentation.quotientEquiv Q split
        (binaryRootData Q split hm hK μ n short d₀ hF hcore hgen)
        (MarkedLocal.endpointMap Q e 0 a) := rfl

theorem binary_comparison_right (a : parabolic L S 1) :
    ((binaryComparison Q split e hm hK μ n short d₀ hF hcore hgen).right a :
      Atlas.G2.Model F) =
      G2Presentation.quotientEquiv Q split
        (binaryRootData Q split hm hK μ n short d₀ hF hcore hgen)
        (MarkedLocal.endpointMap Q e 1 a) := rfl

/-- Both squares hold on the entire original overlap. -/
theorem binary_comparison_squares
    (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    let c := binaryComparison Q split e hm hK μ n short d₀ hF hcore hgen
    c.left ⟨b,b.property.1⟩ = (flagAmalgam F short).left (c.middle b) ∧
    c.right ⟨b,b.property.2⟩ = (flagAmalgam F short).right (c.middle b) :=
  ⟨(binaryComparison Q split e hm hK μ n short d₀ hF hcore hgen).left_commutes b,
    (binaryComparison Q split e hm hK μ n short d₀ hF hcore hgen).right_commutes b⟩

/-- The original S is also carried to the model U by the same equivalence. -/
theorem binary_source_sylow_image :
    (MarkedLocal.sylowMap Q e h).range.map
      (G2Presentation.quotientEquiv Q split
        (binaryRootData Q split hm hK μ n short d₀ hF hcore hgen)).toMonoidHom =
      Atlas.G2.unipotent :=
  G2Presentation.source_sylow_image Q e h split
    (binaryRootData Q split hm hK μ n short d₀ hF hcore hgen)

/-- In the native orientation the same constructed maps reach the published
null-plane and singular-point geometric amalgam. -/
def binaryGeometricComparison
    (dshort : PartialPositiveData (alignedSourceRoots Q split hK μ n 0)) :
    RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      (CFSG.Quasithin.ChapterF.GreenBook.LieModels.G2.geometricAmalgam (F := F)) :=
  G2Presentation.geometricComparison Q e split
    (binaryRootData Q split hm hK μ n 0 dshort hF hcore hgen)

theorem binary_geometric_squares
    (dshort : PartialPositiveData (alignedSourceRoots Q split hK μ n 0))
    (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    let c := binaryGeometricComparison Q split e hm hK μ n hF hcore hgen dshort
    c.left ⟨b,b.property.1⟩ =
      (CFSG.Quasithin.ChapterF.GreenBook.LieModels.G2.geometricAmalgam (F := F)).left
        (c.middle b) ∧
    c.right ⟨b,b.property.2⟩ =
      (CFSG.Quasithin.ChapterF.GreenBook.LieModels.G2.geometricAmalgam (F := F)).right
        (c.middle b) :=
  ⟨(binaryGeometricComparison Q split e hm hK μ n hF hcore hgen dshort).left_commutes b,
    (binaryGeometricComparison Q split e hm hK μ n hF hcore hgen dshort).right_commutes b⟩
end Binary

section Original
variable (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
  (hm₀ : rotationOrder Q₀ = 6)
  (hK₀ : ∀ i, simpleRemainder Q₀ split₀ i ≤ localKernel Q₀ i)
  (μ₀ : ∀ i, localGroup Q₀ split₀ i ≃* PSL(2,F))
  (n₀ : ∀ i, RootReflection Q₀ split₀ i)
  (d₁ : PartialPositiveData (alignedSourceRoots Q₀ split₀ hK₀ μ₀ n₀ short))

include h in
theorem positive_original_quotient :
    ∃ f : Atlas.G2.unipotent (K := F) →* S, Function.Surjective f ∧
      ∀ u, Q₀.q ⟨f u,(show S ≤ generated L S from le_sup_right) (f u).property⟩ =
        (alignedSourceRoots Q₀ split₀ hK₀ μ₀ n₀ short).unipotentHom
          (aligned_positive_relations_of_partial Q₀ split₀ hK₀ μ₀ n₀ short hm₀ d₁).collection u := by
  let hc := aligned_short_centralizes Q₀ split₀ hK₀ μ₀ n₀ short hm₀ d₁.commuting
  refine ⟨ReflectionPositive.sourceSylowHom Q₀ split₀ (originalMarkedIso Q₀)
      hm₀ hK₀ μ₀ n₀ short hc d₁ h,
    ReflectionPositive.sourceSylowHom_surjective Q₀ split₀ (originalMarkedIso Q₀)
      hm₀ hK₀ μ₀ n₀ short hc d₁ h, ?_⟩
  intro u
  have he := ReflectionPositive.sourceSylowHom_quotient Q₀ split₀ (originalMarkedIso Q₀)
    hm₀ hK₀ μ₀ n₀ short hc d₁ h u
  change ((originalMarkedIso Q₀).middle _ : (generated L S) ⧸ Q₀.D) = _ at he
  rwa [originalMarkedIso_middle_apply] at he

variable (hF : Nat.card F = 2) (hcore₀ : Q₀.tits.B.normalCore = ⊥)
  (hgen₀ : split₀.unipotentClosure = ⊤)

/-- The original source specialization follows Q.q at the left endpoint. -/
theorem binary_original_left (a : parabolic L S 0) :
    ((binaryComparison Q₀ split₀ (originalMarkedIso Q₀) hm₀ hK₀ μ₀ n₀ short d₁
      hF hcore₀ hgen₀).left a : Atlas.G2.Model F) =
      G2Presentation.quotientEquiv Q₀ split₀
        (binaryRootData Q₀ split₀ hm₀ hK₀ μ₀ n₀ short d₁ hF hcore₀ hgen₀)
        (Q₀.q ⟨a,parabolic_le_generated 0 a.property⟩) :=
  G2Presentation.originalComparison_left_apply Q₀ split₀
    (binaryRootData Q₀ split₀ hm₀ hK₀ μ₀ n₀ short d₁ hF hcore₀ hgen₀) a

/-- The right endpoint uses its own literal inclusion into the numerator. -/
theorem binary_original_right (a : parabolic L S 1) :
    ((binaryComparison Q₀ split₀ (originalMarkedIso Q₀) hm₀ hK₀ μ₀ n₀ short d₁
      hF hcore₀ hgen₀).right a : Atlas.G2.Model F) =
      G2Presentation.quotientEquiv Q₀ split₀
        (binaryRootData Q₀ split₀ hm₀ hK₀ μ₀ n₀ short d₁ hF hcore₀ hgen₀)
        (Q₀.q ⟨a,parabolic_le_generated 1 a.property⟩) :=
  G2Presentation.originalComparison_right_apply Q₀ split₀
    (binaryRootData Q₀ split₀ hm₀ hK₀ μ₀ n₀ short d₁ hF hcore₀ hgen₀) a

/-- The entire original overlap uses the same quotient map as both endpoints. -/
theorem binary_original_middle
    (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    ((binaryComparison Q₀ split₀ (originalMarkedIso Q₀) hm₀ hK₀ μ₀ n₀ short d₁
      hF hcore₀ hgen₀).middle b : Atlas.G2.Model F) =
      G2Presentation.quotientEquiv Q₀ split₀
        (binaryRootData Q₀ split₀ hm₀ hK₀ μ₀ n₀ short d₁ hF hcore₀ hgen₀)
        (Q₀.q ⟨b,parabolic_le_generated 0 b.property.1⟩) :=
  G2Presentation.originalComparison_middle_apply Q₀ split₀
    (binaryRootData Q₀ split₀ hm₀ hK₀ μ₀ n₀ short d₁ hF hcore₀ hgen₀) b
end Original
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.GTwoSource.OrthogonalSource

