module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.NormalizedRelations
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.GTwoSource.CommonFieldApplication

/-!
# Full marked G₂ comparison from the constructed common-field pinnings

The actual middle pairing selects an orientation and constructs a field
comparison. Relabel the whole long rank-one pinning by that automorphism.
PinningRecovery realizes it in the existing source construction, and
NormalizedRelations supplies every Borel--Weyl equation. Thus no pairing,
polynomial, field-alignment, auxiliary torus or field-size premise remains.
The resulting RootData has the literal source U, both Weyl placements,
highest-root nontriviality and whole-group generation.

Apply the published positive and full presentation comparisons on the same
marked quotient. Both orientations, the full Borel and both parabolics, original
S, the whole overlap and literal Q.q representatives are retained. In particular
the binary target is full G₂(2), and q=4 is included without an exception.

The earlier local PSL₂ models over a common finite characteristic-two field,
radical-to-panel-kernel inclusions, source reflections, Weyl order six and
normal generation by U remain explicit source inputs. Their producers and
6E row selection belong to the earlier structural/final source assembly, not
to a polynomial-relation callback. This constructs the complete conditional
G₂ source-family contract; it does not assert the global classification.

Source: Fong--Seitz I (6E)(a), p.43; II (9.1)--(9.21), pp.211--217;
DGS Theorem D, p.224. The matrix and ordered-exchange conventions are those
of the existing BorelWeylData.Relations consumer.
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
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.GTwoSource.CommonFieldSource
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
  (hgen : split.unipotentClosure = ⊤)

/-- Construct the complete source data from the compatible whole pinnings. -/
def rootData : RootData Q split F (sourceOrientation Q split hK μ hm) where
  data := normalizedBorelWeyl Q split hK μ n (sourceOrientation Q split hK μ hm) hm
    (sourceOrientation_middle_ne_bot Q split hK μ n hm)
  relations := normalizedBorelWeyl_relations Q split hK μ n
    (sourceOrientation Q split hK μ hm) hm (sourceOrientation_middle_ne_bot Q split hK μ n hm)
  generate := sourceBorelWeyl_whole Q split hK
    (normalizedLocalModels Q split hK μ n (sourceOrientation Q split hK μ hm) hm
      (sourceOrientation_middle_ne_bot Q split hK μ n hm)) n
    (sourceOrientation Q split hK μ hm) split.abelian hm hgen
  positive := by
    rw [normalizedBorelWeyl_roots]
    exact roots_generated Q split hm hK μ n
  highest_nontrivial := by
    rw [normalizedBorelWeyl_roots]
    exact normalizedSourceRoots_highest_nontrivial Q split hK μ n
      (sourceOrientation Q split hK μ hm) hm (sourceOrientation_middle_ne_bot Q split hK μ n hm)
  short_placement := (sourceReflection_placements Q split n (sourceOrientation Q split hK μ hm)).1
  long_placement := (sourceReflection_placements Q split n (sourceOrientation Q split hK μ hm)).2

/-- The full comparison uses precisely the previously constructed source coordinates. -/
theorem rootData_roots :
    (rootData Q split hm hK μ n hgen).data.toPositiveRoots = roots Q split hm hK μ n :=
  normalizedBorelWeyl_roots Q split hK μ n (sourceOrientation Q split hK μ hm) hm
    (sourceOrientation_middle_ne_bot Q split hK μ n hm)

include hK μ in
/-- The common field has the original simple-root size at either endpoint. -/
theorem field_card (i : Fin 2) : Nat.card F = Nat.card (simpleRoot Q split i) :=
  (simpleRoot_card Q split i (hK i) (μ i)).symm

/-- The model equivalence preserves the actual normalized field parameters. -/
theorem quotient_root (k : Fin 6) (a : F) :
    G2Presentation.quotientEquiv Q split (rootData Q split hm hK μ n hgen)
      ((roots Q split hm hK μ n).x k a) = (modelData (F := F)).x k a := by
  rw [←rootData_roots Q split hm hK μ n hgen]
  exact quotientEquiv_root Q split _ k a

/-- Apply the existing full comparison with either orientation. -/
def comparison : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    (flagAmalgam F (sourceOrientation Q split hK μ hm)) :=
  G2Presentation.comparison Q e split
    (rootData Q split hm hK μ n hgen)

/-- The same equivalence identifies the full B and both parabolics. -/
theorem subgroup_images :
    let f := G2Presentation.quotientEquiv Q split
      (rootData Q split hm hK μ n hgen)
    split.U.map f.toMonoidHom = Atlas.G2.unipotent ∧
    Q.tits.B.map f.toMonoidHom = Atlas.G2.borel ∧
    (Q.tits.standardParabolic {Q.simple (sourceOrientation Q split hK μ hm)}).map f.toMonoidHom =
      Atlas.G2.LieParabolicSetup.parabolic₁ ∧
    (Q.tits.standardParabolic {Q.simple (1-(sourceOrientation Q split hK μ hm))}).map f.toMonoidHom =
      Atlas.G2.LieParabolicSetup.parabolic₂ :=
  G2Presentation.subgroup_images Q split
    (rootData Q split hm hK μ n hgen)

theorem comparison_left (a : parabolic L S 0) :
    ((comparison Q split e hm hK μ n hgen).left a : Atlas.G2.Model F) =
      G2Presentation.quotientEquiv Q split
        (rootData Q split hm hK μ n hgen)
        (MarkedLocal.endpointMap Q e 0 a) := rfl

theorem comparison_right (a : parabolic L S 1) :
    ((comparison Q split e hm hK μ n hgen).right a : Atlas.G2.Model F) =
      G2Presentation.quotientEquiv Q split
        (rootData Q split hm hK μ n hgen)
        (MarkedLocal.endpointMap Q e 1 a) := rfl

/-- Both squares use the entire original overlap. -/
theorem comparison_squares (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    let c := comparison Q split e hm hK μ n hgen
    c.left ⟨b,b.property.1⟩ = (flagAmalgam F (sourceOrientation Q split hK μ hm)).left (c.middle b) ∧
    c.right ⟨b,b.property.2⟩ = (flagAmalgam F (sourceOrientation Q split hK μ hm)).right (c.middle b) :=
  ⟨(comparison Q split e hm hK μ n hgen).left_commutes b,
    (comparison Q split e hm hK μ n hgen).right_commutes b⟩

/-- Original S maps onto the same model U. -/
theorem source_sylow_image (h : HypothesisF11 L S) :
    (MarkedLocal.sylowMap Q e h).range.map
      (G2Presentation.quotientEquiv Q split
        (rootData Q split hm hK μ n hgen)).toMonoidHom =
      Atlas.G2.unipotent :=
  G2Presentation.source_sylow_image Q e h split
    (rootData Q split hm hK μ n hgen)

include hm in
/-- The same roots retain the published positive map and both original endpoints. -/
theorem positive_marked_application (h : HypothesisF11 L S) :
    ∃ f : Atlas.G2.unipotent (K := F) →* S, Function.Surjective f ∧
      ∀ (i : Fin 2) (a : Fin 6 → F),
        let s := f (Atlas.G2.unipotentEquiv a)
        MarkedLocal.endpointMap Q e i
          ⟨s,(show S ≤ parabolic L S i from le_sup_right.trans le_sup_left) s.property⟩ =
            (roots Q split hm hK μ n).product a :=
by
  let R := roots Q split hm hK μ n
  let rels : R.CharTwoRelations := normalizedSourceRoots_relations Q split hK μ n
    (sourceOrientation Q split hK μ hm) hm (sourceOrientation_middle_ne_bot Q split hK μ n hm)
  have hU := roots_generated Q split hm hK μ n
  refine ⟨G2Presentation.sourceSylowHom Q split R rels hU e h,
    G2Presentation.sourceSylowHom_surjective Q split R rels hU e h, ?_⟩
  intro i a
  exact G2Presentation.sourceSylowHom_endpoint Q split R rels hU e h i a

/-- The native first-short orientation reaches the actual geometric model. -/
def geometricComparison (hshortIndex : (sourceOrientation Q split hK μ hm) = 0) : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    (CFSG.Quasithin.ChapterF.GreenBook.LieModels.G2.geometricAmalgam (F := F)) := by
  exact G2Presentation.geometricComparison Q e split
    (hshortIndex ▸ rootData Q split hm hK μ n hgen)

theorem geometric_squares (hshortIndex : (sourceOrientation Q split hK μ hm) = 0)
    (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    let c := geometricComparison Q split e hm hK μ n hgen hshortIndex
    c.left ⟨b,b.property.1⟩ =
      (CFSG.Quasithin.ChapterF.GreenBook.LieModels.G2.geometricAmalgam (F := F)).left (c.middle b) ∧
    c.right ⟨b,b.property.2⟩ =
      (CFSG.Quasithin.ChapterF.GreenBook.LieModels.G2.geometricAmalgam (F := F)).right (c.middle b) :=
  ⟨(geometricComparison Q split e hm hK μ n hgen hshortIndex).left_commutes b,
    (geometricComparison Q split e hm hK μ n hgen hshortIndex).right_commutes b⟩

section Original
variable {G F : Type*} [Group G] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 6)
  (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
  (μ : ∀ i, localGroup Q split i ≃* PSL(2,F))
  (n : ∀ i, RootReflection Q split i)
  (hgen : split.unipotentClosure = ⊤)


/-- The original left endpoint uses its literal Q.q representative. -/
theorem original_left (a : parabolic L S 0) :
    ((comparison Q split (originalMarkedIso Q) hm hK μ n hgen).left a :
      Atlas.G2.Model F) =
      G2Presentation.quotientEquiv Q split
        (rootData Q split hm hK μ n hgen)
        (Q.q ⟨a,parabolic_le_generated 0 a.property⟩) :=
  G2Presentation.originalComparison_left_apply Q split
    (rootData Q split hm hK μ n hgen) a

/-- The original right endpoint uses its literal Q.q representative. -/
theorem original_right (a : parabolic L S 1) :
    ((comparison Q split (originalMarkedIso Q) hm hK μ n hgen).right a :
      Atlas.G2.Model F) =
      G2Presentation.quotientEquiv Q split
        (rootData Q split hm hK μ n hgen)
        (Q.q ⟨a,parabolic_le_generated 1 a.property⟩) :=
  G2Presentation.originalComparison_right_apply Q split
    (rootData Q split hm hK μ n hgen) a

/-- The whole overlap uses the same quotient map as both endpoints. -/
theorem original_middle (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    ((comparison Q split (originalMarkedIso Q) hm hK μ n hgen).middle b :
      Atlas.G2.Model F) =
      G2Presentation.quotientEquiv Q split
        (rootData Q split hm hK μ n hgen)
        (Q.q ⟨b,parabolic_le_generated 0 b.property.1⟩) :=
  G2Presentation.originalComparison_middle_apply Q split
    (rootData Q split hm hK μ n hgen) b
end Original
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.GTwoSource.CommonFieldSource
