module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.ZeroPairing
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.GTwoSource.RootPairingApplication

/-!
# Binary source comparison with the middle pairing discharged

Fong--Seitz II (9.3) excludes simultaneous vanishing of the two middle
pairings. Choose the orientation whose opposite pairing is zero; its
selected pairing is therefore nonzero. Over the binary field the actual
commutator coefficient is then forced to be multiplication. The existing
RootPairingSource construction supplies all positive and Borel--Weyl
relations, generation, nontriviality and both placements on the same quotient.

No pairing, orthogonal-centralization or polynomial premise remains in
these binary comparisons. The actual linear local models, radical-kernel
inclusions, source reflections, rotation order and whole-group generation
remain earlier source inputs. The finite-field labeling problem for larger
fields is not asserted here. The chosen orientation can be either index;
the full Borel, both endpoints, original S and literal Q.q are retained.

Source: Fong--Seitz I (6E)(a), printed p.43, and II (9.1)--(9.3), p.211.
The binary comparison is with full G₂(2), using the proved presentation
and kernel result, without Thomas recognition or ambient simplicity.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open Atlas.G2.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.GTwoSource.NonzeroPairingSource
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
  (n : ∀ i, RootReflection Q split i)
  (hF : Nat.card F = 2)
  (hgen : split.unipotentClosure = ⊤)

/-- The actual binary pairing supplies the final field equation to the
existing construction of all root relations, generation and placements. -/
def rootData : RootData Q split F (sourceOrientation Q split hK μ hm) :=
  RootPairingSource.rootData Q split hm hK μ n (sourceOrientation Q split hK μ hm) hF
    (sourceOrientation_middle_ne_bot Q split hK μ n hm) hgen

/-- Apply the existing full comparison with either orientation. -/
def comparison : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    (flagAmalgam F (sourceOrientation Q split hK μ hm)) :=
  G2Presentation.comparison Q e split
    (rootData Q split hm hK μ n hF hgen)

/-- The same equivalence identifies the full B and both parabolics. -/
theorem subgroup_images :
    let f := G2Presentation.quotientEquiv Q split
      (rootData Q split hm hK μ n hF hgen)
    split.U.map f.toMonoidHom = Atlas.G2.unipotent ∧
    Q.tits.B.map f.toMonoidHom = Atlas.G2.borel ∧
    (Q.tits.standardParabolic {Q.simple (sourceOrientation Q split hK μ hm)}).map f.toMonoidHom =
      Atlas.G2.LieParabolicSetup.parabolic₁ ∧
    (Q.tits.standardParabolic {Q.simple (1-(sourceOrientation Q split hK μ hm))}).map f.toMonoidHom =
      Atlas.G2.LieParabolicSetup.parabolic₂ :=
  G2Presentation.subgroup_images Q split
    (rootData Q split hm hK μ n hF hgen)

theorem comparison_left (a : parabolic L S 0) :
    ((comparison Q split e hm hK μ n hF hgen).left a : Atlas.G2.Model F) =
      G2Presentation.quotientEquiv Q split
        (rootData Q split hm hK μ n hF hgen)
        (MarkedLocal.endpointMap Q e 0 a) := rfl

theorem comparison_right (a : parabolic L S 1) :
    ((comparison Q split e hm hK μ n hF hgen).right a : Atlas.G2.Model F) =
      G2Presentation.quotientEquiv Q split
        (rootData Q split hm hK μ n hF hgen)
        (MarkedLocal.endpointMap Q e 1 a) := rfl

/-- Both squares use the entire original overlap. -/
theorem comparison_squares (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    let c := comparison Q split e hm hK μ n hF hgen
    c.left ⟨b,b.property.1⟩ = (flagAmalgam F (sourceOrientation Q split hK μ hm)).left (c.middle b) ∧
    c.right ⟨b,b.property.2⟩ = (flagAmalgam F (sourceOrientation Q split hK μ hm)).right (c.middle b) :=
  ⟨(comparison Q split e hm hK μ n hF hgen).left_commutes b,
    (comparison Q split e hm hK μ n hF hgen).right_commutes b⟩

/-- Original S maps onto the same model U. -/
theorem source_sylow_image (h : HypothesisF11 L S) :
    (MarkedLocal.sylowMap Q e h).range.map
      (G2Presentation.quotientEquiv Q split
        (rootData Q split hm hK μ n hF hgen)).toMonoidHom =
      Atlas.G2.unipotent :=
  G2Presentation.source_sylow_image Q e h split
    (rootData Q split hm hK μ n hF hgen)

include hm hF in
/-- The same roots retain the published positive map and both original endpoints. -/
theorem positive_marked_application (h : HypothesisF11 L S) :
    ∃ f : Atlas.G2.unipotent (K := F) →* S, Function.Surjective f ∧
      ∀ (i : Fin 2) (a : Fin 6 → F),
        let s := f (Atlas.G2.unipotentEquiv a)
        MarkedLocal.endpointMap Q e i
          ⟨s,(show S ≤ parabolic L S i from le_sup_right.trans le_sup_left) s.property⟩ =
            (alignedSourceRoots Q split hK μ n (sourceOrientation Q split hK μ hm)).product a :=
by
  exact RootPairingSource.positive_marked_application Q split e hm hK μ n
    (sourceOrientation Q split hK μ hm) hF
    (sourceOrientation_middle_ne_bot Q split hK μ n hm) h

/-- The native first-short orientation reaches the actual geometric model. -/
def geometricComparison (hshortIndex : (sourceOrientation Q split hK μ hm) = 0) : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    (CFSG.Quasithin.ChapterF.GreenBook.LieModels.G2.geometricAmalgam (F := F)) := by
  exact G2Presentation.geometricComparison Q e split
    (hshortIndex ▸ rootData Q split hm hK μ n hF hgen)

theorem geometric_squares (hshortIndex : (sourceOrientation Q split hK μ hm) = 0)
    (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    let c := geometricComparison Q split e hm hK μ n hF hgen hshortIndex
    c.left ⟨b,b.property.1⟩ =
      (CFSG.Quasithin.ChapterF.GreenBook.LieModels.G2.geometricAmalgam (F := F)).left (c.middle b) ∧
    c.right ⟨b,b.property.2⟩ =
      (CFSG.Quasithin.ChapterF.GreenBook.LieModels.G2.geometricAmalgam (F := F)).right (c.middle b) :=
  ⟨(geometricComparison Q split e hm hK μ n hF hgen hshortIndex).left_commutes b,
    (geometricComparison Q split e hm hK μ n hF hgen hshortIndex).right_commutes b⟩

section Original
variable {G F : Type*} [Group G] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 6)
  (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
  (μ : ∀ i, localGroup Q split i ≃* PSL(2,F))
  (n : ∀ i, RootReflection Q split i)
  (hF : Nat.card F = 2)
  (hgen : split.unipotentClosure = ⊤)


/-- The original left endpoint uses its literal Q.q representative. -/
theorem original_left (a : parabolic L S 0) :
    ((comparison Q split (originalMarkedIso Q) hm hK μ n hF hgen).left a :
      Atlas.G2.Model F) =
      G2Presentation.quotientEquiv Q split
        (rootData Q split hm hK μ n hF hgen)
        (Q.q ⟨a,parabolic_le_generated 0 a.property⟩) :=
  G2Presentation.originalComparison_left_apply Q split
    (rootData Q split hm hK μ n hF hgen) a

/-- The original right endpoint uses its literal Q.q representative. -/
theorem original_right (a : parabolic L S 1) :
    ((comparison Q split (originalMarkedIso Q) hm hK μ n hF hgen).right a :
      Atlas.G2.Model F) =
      G2Presentation.quotientEquiv Q split
        (rootData Q split hm hK μ n hF hgen)
        (Q.q ⟨a,parabolic_le_generated 1 a.property⟩) :=
  G2Presentation.originalComparison_right_apply Q split
    (rootData Q split hm hK μ n hF hgen) a

/-- The whole overlap uses the same quotient map as both endpoints. -/
theorem original_middle (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    ((comparison Q split (originalMarkedIso Q) hm hK μ n hF hgen).middle b :
      Atlas.G2.Model F) =
      G2Presentation.quotientEquiv Q split
        (rootData Q split hm hK μ n hF hgen)
        (Q.q ⟨b,parabolic_le_generated 0 b.property.1⟩) :=
  G2Presentation.originalComparison_middle_apply Q split
    (rootData Q split hm hK μ n hF hgen) b
end Original
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.GTwoSource.NonzeroPairingSource
