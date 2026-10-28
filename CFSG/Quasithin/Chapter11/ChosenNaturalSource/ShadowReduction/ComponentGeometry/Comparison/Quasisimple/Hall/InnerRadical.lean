module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall.RadicalImage
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall.ModelRadicals
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall.ModelActors

/-!
# The Hall comparison after inner placement of the radical image

The literal radical intersection and concrete parabolic normalizers now
construct the inner Sylow normalizer required by the Hall argument. Thus
an inner R₁ image supplies the rank-two actor with no Sylow, normalizer,
or rank witness supplied by the caller. The chosen-flag application uses
the original 11.1.5 dichotomy and natural fixed-space contradiction.

Inner placement and strict omega-center containment remain mathematical
obligations of qt-d-1222-shadow-component-comparison. Earlier-source inputs
retain final discharge by qt-d-1222-shadow-components. This is an increment
of the 11.4.2 proof, not its unconditional conclusion.
Source: Aschbacher--Smith 11.4.2, printed p.777.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

/-- The full inner Sylow normalizer is constructed from the actual radical
core identity and the surviving model, once R₁* is inner. -/
theorem exists_model_normalizer_of_inner_radical
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G)) (hm : RankTwoModel E)
    (hinner : (radical E).map (projection E) ≤ (component E).map (projection E)) :
    ∃ P : Sylow 2 ((component E).map (projection E)),
      (normalizer (P : Set ((component E).map (projection E)))).map
        ((component E).map (projection E)).subtype ≤
      normalizer ((radical E).map (projection E) : Set (ActionQuotient E)) := by
  let B := (component E).map (projection E)
  let U := ((radical E).map (projection E)).subgroupOf B
  obtain ⟨P,hP⟩ := rankTwo_exists_sylow_normalizer E hm U
    (radical_image_intersection_normalizer_core E h hf hne hstar hcent)
  refine ⟨P,(map_mono hP).trans ?_⟩
  have hn := U.le_normalizer_map B.subtype
  rwa [map_subgroupOf_eq_of_le hinner] at hn

/-- The actual odd-primary rank-two actor, with all normalizer choices
supplied by the model and the literal inner radical image. -/
theorem exists_odd_actor_of_inner_radical
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G)) (hm : RankTwoModel E)
    (hinner : (radical E).map (projection E) ≤ (component E).map (projection E)) :
    ∃ (p : ℕ) (Y : Subgroup G), p.Prime ∧ Odd p ∧ p ∣ 2 ^ E.input.field.degree - 1 ∧
      Y ≤ E.Kz ∧ Y ≤ normalizer (E.R₁ : Set G) ∧ IsPGroup p Y ∧ 2 ≤ primeRank p Y := by
  obtain ⟨P,hP⟩ := exists_model_normalizer_of_inner_radical E h hf hne hstar hcent hm hinner
  exact exists_odd_actor_of_model_normalizer E h hf hne hstar hcent hm P hP

variable {E}

/-- The literal chosen-flag contradiction with inner Sylow normalization
proved from the radical image. Innerness and the omega-center inequality
remain local obligations of this owner. -/
theorem ofFlag_false_of_inner_radical_geometry
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
    (hm : RankTwoModel (ofFlag S f X z H))
    (hinner : (radical (ofFlag S f X z H)).map (projection (ofFlag S f X z H)) ≤
      (component (ofFlag S f X z H)).map (projection (ofFlag S f X z H)))
    (hradical : Source.RadicalNormalizerAlternative (T : Subgroup G) V
      (ofFlag S f X z H).V₁ (ofFlag S f X z H).R₁ (normalizer (L : Set G)) L S.field.degree)
    (hZ : (ofFlag S f X z H).V₁ ≠ omegaOneAmbient
      ((center (ofFlag S f X z H).R₁).map (ofFlag S f X z H).R₁.subtype))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      ∀ y ∈ normalizer (L : Set G), orderOf y = 3 → y ∈ L) : False := by
  obtain ⟨P,hP⟩ := exists_model_normalizer_of_inner_radical (ofFlag S f X z H)
    h (fixed_and_transitive D S _ hlinear h1132).1 hne hstar hcent hm hinner
  exact ofFlag_false_of_model_normalizer_geometry S f X z H h hne hstar
    hlinear h1132 hcent hm P hP hradical hZ hcubic

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall
