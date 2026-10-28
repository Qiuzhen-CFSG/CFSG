module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification.LieModels

/-!
# The complete quasisimple FF image sieve in 11.4.2

The full 11.1.1 catalogue and the actual Thompson FF witness determine
SL₃(q), Sp₄(q), G₂(q), or A₇ at q=4 on the literal component image.
The completed A₇ contradiction then leaves precisely the rank-two models
needed by the Hall/Cartan branch. Covers, odd extensions, Ree and both
triality field parameters are included in the comparison.

The full earlier component catalogue, geometry and maximality are explicit
source inputs. The parent qt-d-1222-shadow-components discharges the earlier
geometry and common seed marking; this comparison owner retains maximality
and the Hall/Cartan argument. This is the complete image sieve, not yet
the full component equality. Source: Aschbacher--Smith 11.4.2, pp.776--777.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification
open LocalGeometry.Components
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}

/-- The characteristic-two Lie comparison on the original flag, with the
FF witness discharged by its original Thompson reduction. -/
theorem ofFlag_rankTwo_of_lie
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
    (hm : LieOvergroup ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)
      S.field.degree) : RankTwoModel (ofFlag S f X z H) := by
  obtain ⟨_,_,_,_,_,hff,_⟩ := ofFlag_ff_reduction S f X z H h hne hstar
    hlinear h1132 hcent hline hXR
  exact rankTwo_image_of_lie _ h (fixed_and_transitive D S _ hlinear h1132).1
    hne hstar hcent hff hm

/-- Complete B.4/B.5 comparison of every 11.1.1 constructor, at the original
field and the literal component action image. No image-model input remains. -/
theorem ofFlag_survivingModels
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
      S.field.degree) : SurvivingModels (ofFlag S f X z H) := by
  cases hm with
  | equal he =>
    exact ((h.strict_comparison (fixed_and_transitive D S _ hlinear h1132).1 hne).2.1.ne he).elim
  | lie hl =>
    exact Or.inl (ofFlag_rankTwo_of_lie S f X z H h hne hstar
      hlinear h1132 hcent hline hXR hl)
  | four hq hm =>
    exact Or.inr ⟨hq,ofFlag_fieldFour_image S f X z H h hne hstar
      hlinear h1132 hcent hline hXR hm⟩

/-- After the proved A₇ contradiction, a strict quasisimple comparison has
one of the three rank-two images required by the remaining Hall argument. -/
theorem ofFlag_rankTwo_of_componentAlternative
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
    RankTwoModel (ofFlag S f X z H) := by
  rcases ofFlag_survivingModels S f X z H h hne hstar hlinear h1132 hcent hline hXR hm
    with hr | ha
  · exact hr
  · exact (AlternatingSeven.ofFlag_false S f X z H h hne hstar
      hlinear h1132 hcent hline hXR ha e).elim

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification
