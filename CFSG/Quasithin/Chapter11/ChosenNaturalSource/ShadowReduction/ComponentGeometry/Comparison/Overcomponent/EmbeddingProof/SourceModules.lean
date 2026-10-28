module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.AlternatingSeven
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.OddExtensions
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.PrimeExtensions
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.ModuleExclusions
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification.FieldFour

/-!
# The full containing catalogue in the normalized-module comparison

Every proper maximal overcomponent has quasisimple two-core quotient and
lies in the original field-four catalogue. B.4/B.5 central-quotient
restrictions reduce that complete catalogue to A₇ or its three-cover;
the actual seed--point chain excludes both. Applying this to the genuine
chosen seed and doubled orbit excludes FF actions, and the same comparison
excludes the orthogonal-minus alternative. No six-pair embedding premise
is required for this negative comparison.

The maximality endpoint constructs a chosen module for the literal
maximal container and contradicts its positive normalized alternative.
It retains exactly the earlier 3.2.5 and positive normalized-module inputs:
qt-baumann-fsu and qt-d-1222-normalized-nonff remain their producers, with
final discharge by qt-d-1222-shadow-components. This does not complete
11.4.2: the Hall inner-placement and strict omega-center arguments remain
with qt-d-1222-shadow-component-comparison. The original proper-pair exports
also remain available as a separate source comparison obligation.
Source: Aschbacher--Smith 11.4.2, p.776, using 3.2.5, 7.0.1 and B.4/B.5.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
open Quasisimple.Classification ModuleExclusions
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D₀ : Chapter12.Section02.ChosenModule T L V}

/-- Direct comparison with the complete containing catalogue excludes the
B.4/B.5 restrictions, with no proper-pair shortlist premise. -/
theorem ofFlag_not_centralQuotientRestrictions
    (S : D₀.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D₀ S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D₀ S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D₀ S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J)
    : ¬ CentralQuotientRestrictions ((J ⧸ pCore 2 J) ⧸ center (J ⧸ pCore 2 J)) := by
  let := ofFlag_proper_overcomponent_quasisimple S f X z H h hne hlinear h1132 e hcent hJ hlt
  have hm := (ofFlag_proper_overcomponent_fieldFour S f X z H h hne hlinear h1132 e hJ.1 hlt).2
  intro hr
  exact ofFlag_not_alternating_seven_overcomponent S f X z H h hne hlinear h1132 e hJ.1 hlt
    (fieldFour_alternating (pCore_quotient_pCore_eq_bot 2) hr hm)

/-- All negative module comparisons on any actual chosen module for the
proper overcomponent. Quasisimplicity and the containing catalogue are proved. -/
theorem ofFlag_negative_modules_of_catalogue
    (S : D₀.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D₀ S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D₀ S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D₀ S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J)
    {W : Subgroup G} (D : Chapter12.Section02.ChosenModule T J W) :
    (¬ IsFFModule (normalizerRepresentation D.chosenAction)) ∧
      (D.MarkedDoubled → ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) ∧
      ¬ Chapter7.NormalizedSource.OrthogonalMinusAlternative
        D.orbitRepresentation D.orbitComponent := by
  have hq := ofFlag_proper_overcomponent_quasisimple S f X z H h hne hlinear h1132 e hcent hJ hlt
  have hs := (source_hypotheses h hJ hlt hq).toHypothesis1221
  have hr := ofFlag_not_centralQuotientRestrictions S f X z H h hne hlinear h1132 e hcent hJ hlt
  exact ⟨fun hff => hr (seed_restrictions D hs hff),
    fun hd hff => hr (doubled_restrictions D hs hd hff),
    fun ho => hr (orthogonal_restrictions D hs ho)⟩

/-- The original full orbit contradicts its positive normalized-source
alternative. The exact earlier 3.2.5 alternatives still retain their producer. -/
theorem ofFlag_false_of_normalized_source
    (S : D₀.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D₀ S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D₀ S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D₀ S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J)
    {W : Subgroup G} (D : Chapter12.Section02.ChosenModule T J W)
    (h325 : D.Source325Alternatives)
    (halt : IsFFModule D.sourceOrbitNormalizerRepresentation ∨
      Chapter7.NormalizedSource.OrthogonalMinusAlternative
        D.orbitRepresentation D.orbitComponent) : False := by
  obtain ⟨hnseed,hndouble,hnorth⟩ :=
    ofFlag_negative_modules_of_catalogue S f X z H h hne hlinear h1132 e hcent hJ hlt D
  rcases halt with hff | ho
  · rcases h325 with ⟨hW,_⟩ | ⟨hW,_,_⟩ | hd
    · have he : W = D.sourceOrbit := by rw [D.sourceOrbit_eq,hW]
      exact hnseed ((D.chosen_normalizer_ff_iff_orbit_of_eq he).mpr hff)
    · have he : W = D.sourceOrbit := by rw [D.sourceOrbit_eq,hW]
      exact hnseed ((D.chosen_normalizer_ff_iff_orbit_of_eq he).mpr hff)
    · exact hndouble hd hff
  · exact hnorth ho

/-- Maximality of the original point component from the two exact earlier
module-source implications. The normalized alternative is owned by
qt-d-1222-normalized-nonff and 3.2.5 by qt-baumann-fsu; final discharge stays
with qt-d-1222-shadow-components. No embedding or negative-model premise remains. -/
theorem ofFlag_point_mem_LStar_of_normalized_source
    (S : D₀.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D₀ S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D₀ S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D₀ S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (h325 : ∀ (J : Subgroup G),
      Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J →
      ∀ (W : Subgroup G) (D : Chapter12.Section02.ChosenModule T J W), D.Source325Alternatives)
    (hpositive : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      ∀ (J : Subgroup G),
      Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J →
      ∀ (W : Subgroup G) (D : Chapter12.Section02.ChosenModule T J W),
        IsFFModule D.sourceOrbitNormalizerRepresentation ∨
          Chapter7.NormalizedSource.OrthogonalMinusAlternative D.orbitRepresentation D.orbitComponent) :
    (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G) := by
  obtain ⟨J,hJ,hle⟩ := h.exists_maximal_overcomponent
  by_cases he : (ofFlag S f X z H).Kz = J
  · exact he.symm ▸ hJ
  have hlt := lt_of_le_of_ne hle he
  have hq := ofFlag_proper_overcomponent_quasisimple S f X z H h hne hlinear h1132 e hcent hJ hlt
  obtain ⟨hs,W,⟨D⟩⟩ := exists_chosenModule h hJ hlt hq
  exact (ofFlag_false_of_normalized_source S f X z H h hne hlinear h1132 e hcent hJ hlt D
    (h325 J hs W D) (hpositive S.many J hs W D)).elim

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
