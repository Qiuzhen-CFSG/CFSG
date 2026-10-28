module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.OmegaCenterComparison
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall.LinearThreeOmega

/-!
# Original equality in the SL₃ point-image branch

The whole-center calculation gives V₁ < Ω₁Z(R₁) on the original flag when
the point-component action image is SL₃(q). The original radical-normalizer
alternative then puts N_G(R₁) inside N_G(L), and the completed point-fixed
Hall argument yields Kz = K. Source 3.2.5 is instantiated using S.many.

The remaining-case theorem retains all original block clauses and confines
the point image to Sp₄(q) or G₂(q). Their center calculations remain with
qt-d-1222-shadow-component-comparison. The positive normalized-module
implication retains qt-d-1222-normalized-nonff; earlier geometry and final
source discharge retain qt-d-1222-shadow-components. This is not full 11.4.2.
Source: Aschbacher–Smith 11.4.2, printed p.777, using 11.1.5 and B.5.1.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison
open Quasisimple Quasisimple.Hall Quasisimple.Classification Overcomponent.EmbeddingProof
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}

/-- The only remaining escaping-normalizer comparisons have a symplectic
or G₂ point image. The original block and every original omega-center and
normalizer clause are retained; the SL₃ image is excluded by the constructed
natural submodule, without an additional action or cardinality premise. -/
theorem ofFlag_eq_or_nonlinear_omega_block
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hXR : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G))
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      PSL(2,S.field.Carrier))
    (hpositive : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      ∀ (J : Subgroup G),
      Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J →
      ∀ (W : Subgroup G) (D : Chapter12.Section02.ChosenModule T J W),
        IsFFModule D.sourceOrbitNormalizerRepresentation ∨
          Chapter7.NormalizedSource.OrthogonalMinusAlternative D.orbitRepresentation D.orbitComponent)
    (hradical : Source.RadicalNormalizerAlternative (T : Subgroup G) V
      (ofFlag S f X z H).V₁ (ofFlag S f X z H).R₁ (normalizer (L : Set G)) L S.field.degree) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K ∨
      (((ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L) ∧
        V = Source.conjugateSpan (normalizer (L : Set G)) V ∧
        (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ ∧
        (ofFlag S f X z H).V₁ = radicalOmega (ofFlag S f X z H) ∧
        ¬ normalizer ((ofFlag S f X z H).R₁ : Set G) ≤ normalizer (L : Set G)) ∧
      (Source.IsSp (componentImage (ofFlag S f X z H)) 2 (2^S.field.degree) ∨
        ClassificationModels.IsG2At (componentImage (ofFlag S f X z H)) (2^S.field.degree))) := by
  have h325 := fun (J : Subgroup G)
    (hJ : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J)
    (W : Subgroup G) (D' : Chapter12.Section02.ChosenModule T J W) =>
      D'.source325_of_many hJ S.many
  by_cases hne : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K
  · exact .inl hne
  obtain he | hb := ofFlag_eq_or_block_of_normalized_source S f X z H h hlinear h1132
    hcent hline hXR e h325 hpositive hradical
  · exact .inl he
  have hs := ofFlag_point_mem_LStar_of_normalized_source S f X z H h hne hlinear h1132 e hcent
    h325 hpositive
  let := ofFlag_point_quasisimple_of_maximal S f X z H h hlinear h1132 hcent hline hXR e hne hs
  have hc := ofFlag_overcomponent_alternative S f X z H e h.point_mem_local_family le_rfl
  have hm := Quasisimple.Classification.ofFlag_rankTwo_of_componentAlternative
    S f X z H h hne hs hlinear h1132 hcent hline hXR hc e
  refine .inr ⟨hb,?_⟩
  rcases hm with hsl | hsp | hg
  · have hlt := ofFlag_linearThree_line_lt_radicalOmega S f X z H h hne hs hlinear h1132
      hcent hline hXR e hsl
    exact (hlt.ne hb.2.2.2.1).elim
  · exact .inl hsp
  · exact .inr hg

/-- The SL₃ point-image branch of the original equality, with maximality,
quasisimplicity, natural submodule selection and the strict omega-center
step all discharged internally. The normalized-source and earlier geometry
inputs retain their original final assembly owners. -/
theorem ofFlag_eq_of_linearThree_image_of_positive_source
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hXR : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G))
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      PSL(2,S.field.Carrier))
    (hpositive : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      ∀ (J : Subgroup G),
      Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J →
      ∀ (W : Subgroup G) (D : Chapter12.Section02.ChosenModule T J W),
        IsFFModule D.sourceOrbitNormalizerRepresentation ∨
          Chapter7.NormalizedSource.OrthogonalMinusAlternative D.orbitRepresentation D.orbitComponent)
    (hradical : Source.RadicalNormalizerAlternative (T : Subgroup G) V
      (ofFlag S f X z H).V₁ (ofFlag S f X z H).R₁ (normalizer (L : Set G)) L S.field.degree)
    (hsl : Source.IsSL (componentImage (ofFlag S f X z H)) 3 (2^S.field.degree)) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K := by
  have h325 := fun (J : Subgroup G)
    (hJ : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J)
    (W : Subgroup G) (D' : Chapter12.Section02.ChosenModule T J W) =>
      D'.source325_of_many hJ S.many
  by_contra hne
  have hs := ofFlag_point_mem_LStar_of_normalized_source S f X z H h hne hlinear h1132 e hcent
    h325 hpositive
  let := ofFlag_point_quasisimple_of_maximal S f X z H h hlinear h1132 hcent hline hXR e hne hs
  have hlt := ofFlag_linearThree_line_lt_radicalOmega S f X z H h hne hs hlinear h1132
    hcent hline hXR e hsl
  have hNM : normalizer ((ofFlag S f X z H).R₁ : Set G) ≤ normalizer (L : Set G) := by
    rcases hradical with hn | hb
    · exact hn
    · exact (hlt.ne hb.2.2.2).elim
  exact hne (ofFlag_eq_of_normalizer_of_positive_source S f X z H h hlinear h1132
    hcent hline hXR e hpositive hNM)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison
