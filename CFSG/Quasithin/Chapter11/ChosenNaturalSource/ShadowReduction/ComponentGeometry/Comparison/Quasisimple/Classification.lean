module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification.Sporadic
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification.Lie
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall.Intersection
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall.ModelActors
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall.InnerRadical
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall.G2Inner

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall.SeedFrame
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall.SeedEquality
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall.Sp4Inner
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall.RankTwoInner

/-!
# The complete quasisimple FF image comparison in 11.4.2

On the original chosen flag, the proved Thompson reduction supplies the
FF witness. Theorem A and complete B.5.1 supply all source action clauses
and the literal component-image catalogue. Central-quotient restrictions
preserve covering kernels and apply also to reducible actions. Comparing
the full exceptional field-four list leaves an actual A7 action image,
whose completed field-automorphism contradiction proves component equality.
The Lie comparison excludes Ree and both triality parameters and identifies
the remaining literal image as SL₃(q), Sp₄(q), or G₂(q), retaining q.

The original quotient and full Sylow normalization identify the perfect
seed with a whole marked local and its normalizer with the full parabolic.
Its trivial radical action on the local quotient proves inner placement of
R₁* in all three surviving component images, including G₂ in even degree.
The radical-intersection calculation then constructs a full inner Sylow
normalizer and an odd-primary actor of rank two.

When the original natural module is G₂, 11.1.5 gives ambient normalization
and 11.0.4 puts this actor in L. The actual chosen-flag consumer proves
Kz = K for all surviving image rows. For the other original natural actions,
strict omega-center containment remains with
qt-d-1222-shadow-component-comparison. The full proper-pair catalogue is
retained by the separate overcomponent comparison. These results do not yet
establish
the full source equality. Source: Aschbacher--Smith 11.4.2, pp.776--777.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

variable {E}

/-- B.5.1 on the actual chosen flag, with its FF witness proved internally. -/
theorem ofFlag_source_classification
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hstar : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)]
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hXR : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G)) :
    let E := ofFlag S f X z H
    componentImage E ≤ offenderGroup E ∧
    Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (offenderAction E) (offenderComponent E)) := by
  obtain ⟨_,_,_,_,_,hff,_⟩ := ofFlag_ff_reduction S f X z H h hne hstar
    hlinear h1132 hcent hline hXR
  exact source_classification _ h (fixed_and_transitive D S _ hlinear h1132).1
    hne hstar hcent hff

/-- The complete B.4/B.5 actor list on the original centralizer quotient. -/
theorem ofFlag_image_model
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hstar : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)]
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hXR : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G)) :
    ImageModel (componentImage (ofFlag S f X z H)) := by
  obtain ⟨hK,⟨d⟩⟩ := ofFlag_source_classification S f X z H h hne hstar
    hlinear h1132 hcent hline hXR
  exact (image_model_of_source d).of_mulEquiv (subgroupOfEquivOfLe hK).symm

/-- The Mathieu and Janko rows of the full 11.1.1 input are impossible
on the actual chosen flag. No FF or representation-classification input remains. -/
theorem ofFlag_not_m23_or_j4_quotient
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hstar : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)]
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hXR : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G)) :
    let Q := (ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz
    ¬ Nonempty (Q ≃* Sporadic.Mathieu.M23) ∧ ¬ Nonempty (Q ≃* Janko4.Model) := by
  obtain ⟨_,_,_,_,_,hff,_⟩ := ofFlag_ff_reduction S f X z H h hne hstar
    hlinear h1132 hcent hline hXR
  have hf := (fixed_and_transitive D S _ hlinear h1132).1
  exact ⟨not_m23_quotient _ h hf hne hstar hcent hff,
    not_j4_quotient _ h hf hne hstar hcent hff⟩

/-- The full image sieve feeds the constructed Hall actor on the original
flag. The two displayed normalizer/omega-center premises are the remaining
local geometric steps of this owner, not claims of completed source results. -/
theorem ofFlag_eq_of_normalizer_geometry
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hstar : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)]
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hXR : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G))
    (hm : LocalGeometry.Components.ComponentAlternative
      (ofFlag S f X z H).L₁ (ofFlag S f X z H).Kz S.field.degree)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    (P : Sylow 2 ((component (ofFlag S f X z H)).map (projection (ofFlag S f X z H))))
    (hN : (normalizer (P : Set ((component (ofFlag S f X z H)).map
        (projection (ofFlag S f X z H))))).map
        ((component (ofFlag S f X z H)).map (projection (ofFlag S f X z H))).subtype ≤
      normalizer ((radical (ofFlag S f X z H)).map (projection (ofFlag S f X z H)) :
        Set (ActionQuotient (ofFlag S f X z H))))
    (hradical : Source.RadicalNormalizerAlternative (T : Subgroup G) V
      (ofFlag S f X z H).V₁ (ofFlag S f X z H).R₁ (normalizer (L : Set G)) L S.field.degree)
    (hZ : (ofFlag S f X z H).V₁ ≠ omegaOneAmbient
      ((center (ofFlag S f X z H).R₁).map (ofFlag S f X z H).R₁.subtype))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      ∀ y ∈ normalizer (L : Set G), orderOf y = 3 → y ∈ L) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K := by
  by_contra hne
  have hmodel := ofFlag_rankTwo_of_componentAlternative S f X z H h hne hstar
    hlinear h1132 hcent hline hXR hm e
  exact Hall.ofFlag_false_of_model_normalizer_geometry S f X z H h hne hstar
    hlinear h1132 hcent hmodel P hN hradical hZ hcubic

/-- The source image sieve supplies the model, and the radical-intersection
proof constructs its full inner Sylow normalizer. The remaining local
premises are innerness of R₁* and strict omega-center containment; earlier
source discharge remains with qt-d-1222-shadow-components. -/
theorem ofFlag_eq_of_inner_radical_geometry
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hstar : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)]
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hXR : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G))
    (hm : LocalGeometry.Components.ComponentAlternative
      (ofFlag S f X z H).L₁ (ofFlag S f X z H).Kz S.field.degree)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    (hinner : (radical (ofFlag S f X z H)).map (projection (ofFlag S f X z H)) ≤
      (component (ofFlag S f X z H)).map (projection (ofFlag S f X z H)))
    (hradical : Source.RadicalNormalizerAlternative (T : Subgroup G) V
      (ofFlag S f X z H).V₁ (ofFlag S f X z H).R₁ (normalizer (L : Set G)) L S.field.degree)
    (hZ : (ofFlag S f X z H).V₁ ≠ omegaOneAmbient
      ((center (ofFlag S f X z H).R₁).map (ofFlag S f X z H).R₁.subtype))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      ∀ y ∈ normalizer (L : Set G), orderOf y = 3 → y ∈ L) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K := by
  by_contra hne
  have hmodel := ofFlag_rankTwo_of_componentAlternative S f X z H h hne hstar
    hlinear h1132 hcent hline hXR hm e
  exact Hall.ofFlag_false_of_inner_radical_geometry S f X z H h hne hstar
    hlinear h1132 hcent hmodel hinner hradical hZ hcubic


open CFSG.Quasithin.ChapterB.QuasisimpleSource

/-- For an original G₂ natural module of odd field degree, the complete
component sieve now leaves only the linear-three and symplectic-four
images in a strict comparison. The G₂ image is excluded by the actual
Hall actor, with inner placement and ambient normalization discharged. -/
theorem ofFlag_odd_g2_remaining_models
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hstar : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)]
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hXR : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G))
    (hm : LocalGeometry.Components.ComponentAlternative
      (ofFlag S f X z H).L₁ (ofFlag S f X z H).Kz S.field.degree)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    (ho : Odd S.field.degree)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (hradical : Source.RadicalNormalizerAlternative (T : Subgroup G) V
      (ofFlag S f X z H).V₁ (ofFlag S f X z H).R₁ (normalizer (L : Set G)) L S.field.degree) :
    Source.IsSL (componentImage (ofFlag S f X z H)) 3 (2 ^ S.field.degree) ∨
      Source.IsSp (componentImage (ofFlag S f X z H)) 2 (2 ^ S.field.degree) := by
  rcases ofFlag_rankTwo_of_componentAlternative S f X z H h hne hstar hlinear h1132
      hcent hline hXR hm e with hsl | hsp | hg
  · exact .inl hsl
  · exact .inr hsp
  · exact (hne (Hall.ofFlag_g2_eq_of_odd_g2 S f X z H h hstar hlinear h1132
      hcent hg ho m hradical)).elim

/-- The original chosen flag has a concrete parabolic seed frame in every
surviving Hall model. The source image sieve, full Sylow invariance and
11.4.1 fixed-space conclusion are discharged here. The actual radical
acts trivially on the preserved PSL₂ quotient of the same seed image. -/
theorem ofFlag_seed_parabolic_frame
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hstar : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)]
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hXR : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G))
    (hm : LocalGeometry.Components.ComponentAlternative (ofFlag S f X z H).L₁ (ofFlag S f X z H).Kz
      S.field.degree)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier) :
    let E := ofFlag S f X z H
    Nonempty ((Hall.SeedFrame.seed E ⧸ pCore 2 (Hall.SeedFrame.seed E)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier) ∧
      Hall.SeedFrame.ParabolicFrame E ∧
      ⁅(radical E).map (projection E), Hall.SeedFrame.seed E⁆ ≤
        (Hall.SeedFrame.seed E).pCoreIn 2 := by
  have hf := (fixed_and_transitive D S _ hlinear h1132).1
  have hT : (T : Subgroup G) ≤ (ofFlag S f X z H).G₁ := f.invariant 0
  have hr := ofFlag_rankTwo_of_componentAlternative S f X z H h hne hstar
    hlinear h1132 hcent hline hXR hm e
  exact ⟨⟨Hall.SeedFrame.seedQuotientEquiv _ h hf hne hstar hcent e⟩,
    Hall.SeedFrame.parabolic_frame _ h hf hne hstar hcent e hT hr,
    Hall.SeedFrame.radical_seed_commutator_le_core _ hT⟩

/-- The original chosen flag has the full seed/local and normalizer/parabolic
equalities, with the original quotient marking and radical commutator retained. -/
theorem ofFlag_full_seed_parabolic_frame
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hstar : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)]
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hXR : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G))
    (hm : LocalGeometry.Components.ComponentAlternative (ofFlag S f X z H).L₁ (ofFlag S f X z H).Kz
      S.field.degree)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier) :
    let E := ofFlag S f X z H
    Nonempty ((Hall.SeedFrame.seed E ⧸ pCore 2 (Hall.SeedFrame.seed E)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier) ∧
      Hall.SeedFrame.FullParabolicFrame E ∧
      ⁅(radical E).map (projection E), Hall.SeedFrame.seed E⁆ ≤
        (Hall.SeedFrame.seed E).pCoreIn 2 := by
  have hf := (fixed_and_transitive D S _ hlinear h1132).1
  have hT : (T : Subgroup G) ≤ (ofFlag S f X z H).G₁ := f.invariant 0
  have hr := ofFlag_rankTwo_of_componentAlternative S f X z H h hne hstar
    hlinear h1132 hcent hline hXR hm e
  exact ⟨⟨Hall.SeedFrame.seedQuotientEquiv _ h hf hne hstar hcent e⟩,
    Hall.SeedFrame.full_parabolic_frame _ h hf hne hstar hcent e hT hr,
    Hall.SeedFrame.radical_seed_commutator_le_core _ hT⟩

/-- On the original G₂ natural action, the actual Hall contradictions exclude
all symplectic images and the odd-degree G₂ images. The complete source sieve
therefore leaves only SL₃, or G₂ in even degree, under strict comparison. -/
theorem ofFlag_g2_remaining_models
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hstar : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)]
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hXR : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G))
    (hm : LocalGeometry.Components.ComponentAlternative
      (ofFlag S f X z H).L₁ (ofFlag S f X z H).Kz S.field.degree)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (hradical : Source.RadicalNormalizerAlternative (T : Subgroup G) V
      (ofFlag S f X z H).V₁ (ofFlag S f X z H).R₁ (normalizer (L : Set G)) L S.field.degree) :
    Source.IsSL (componentImage (ofFlag S f X z H)) 3 (2 ^ S.field.degree) ∨
      (ClassificationModels.IsG2At (componentImage (ofFlag S f X z H)) (2 ^ S.field.degree) ∧
        Even S.field.degree) := by
  rcases ofFlag_rankTwo_of_componentAlternative S f X z H h hne hstar hlinear h1132
      hcent hline hXR hm e with hsl | hsp | hg
  · exact .inl hsl
  · exact (hne (Hall.ofFlag_g2_eq_of_sp4 S f X z H h hstar hlinear h1132
      hcent e hsp m hradical)).elim
  · refine .inr ⟨hg, Nat.not_odd_iff_even.mp ?_⟩
    intro ho
    exact hne (Hall.ofFlag_g2_eq_of_odd_g2 S f X z H h hstar hlinear h1132
      hcent hg ho m hradical)

/-- For an original G₂ natural action, the full component sieve and the
proved radical placement give the actual equality in every image row. -/
theorem ofFlag_g2_eq
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hstar : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)]
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hXR : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G))
    (hm : LocalGeometry.Components.ComponentAlternative
      (ofFlag S f X z H).L₁ (ofFlag S f X z H).Kz S.field.degree)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (hradical : Source.RadicalNormalizerAlternative (T : Subgroup G) V
      (ofFlag S f X z H).V₁ (ofFlag S f X z H).R₁ (normalizer (L : Set G)) L S.field.degree) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K := by
  by_contra hne
  have hmodel := ofFlag_rankTwo_of_componentAlternative S f X z H h hne hstar
    hlinear h1132 hcent hline hXR hm e
  exact hne (Hall.ofFlag_g2_eq_of_rankTwo S f X z H h hstar hlinear h1132
    hcent e hmodel m hradical)

/-- The literal chosen-flag Hall comparison now needs no inner-placement or
Sylow-normalizer input. Strict omega-center containment remains a local
obligation of this comparison owner; the earlier-source inputs retain their
existing final discharge owner. -/
theorem ofFlag_eq_of_omega_center_geometry
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hstar : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)]
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hXR : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G))
    (hm : LocalGeometry.Components.ComponentAlternative
      (ofFlag S f X z H).L₁ (ofFlag S f X z H).Kz S.field.degree)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    (hradical : Source.RadicalNormalizerAlternative (T : Subgroup G) V
      (ofFlag S f X z H).V₁ (ofFlag S f X z H).R₁ (normalizer (L : Set G)) L S.field.degree)
    (hZ : (ofFlag S f X z H).V₁ ≠ omegaOneAmbient
      ((center (ofFlag S f X z H).R₁).map (ofFlag S f X z H).R₁.subtype))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      ∀ y ∈ normalizer (L : Set G), orderOf y = 3 → y ∈ L) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K := by
  by_contra hne
  have hmodel := ofFlag_rankTwo_of_componentAlternative S f X z H h hne hstar
    hlinear h1132 hcent hline hXR hm e
  have hinner := Hall.rankTwo_radical_image_le_component (ofFlag S f X z H)
    h (fixed_and_transitive D S _ hlinear h1132).1 hne hstar hcent (f.invariant 0) e hmodel
  exact Hall.ofFlag_false_of_inner_radical_geometry S f X z H h hne hstar
    hlinear h1132 hcent hmodel hinner hradical hZ hcubic


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification
