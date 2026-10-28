module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.LinearThreeOmegaComparison
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall.NonlinearOmega

/-!
# The original chosen-flag component equality

The full earlier-source reduction handles proper overcomponents, nonquasisimple
quotients and the A₇ endpoint. In the remaining rank-two images the whole radical
omega-center strictly contains the original field line. For SL₃ this uses an
embedded natural submodule; for Sp₄ and G₂ fixed-vector lifting through the
literal central cover suffices. The original radical-normalizer alternative
therefore puts the point-fixed Hall actor in N_G(L), where the proved Cartan
argument completes equality of the two actual conjugate spans.

Source 3.2.5 is supplied at the same T by S.many. The positive normalized-module
implication remains an earlier input owned by qt-d-1222-normalized-nonff; this
module does not prove that implication. EarlierGeometry, the full 11.3.2,
Cartan line identity, R₁ normalization, seed PSL₂ marking and 11.1.5 alternative
retain final discharge with qt-d-1222-shadow-components. No maximality, FF,
quasisimplicity, shortened catalogue or model-action callback remains.

Lean Kz is source K and Lean K is source K₁. All component normality remains
relative to the point centralizer or line normalizer.
Source: Aschbacher–Smith 11.4.2, printed pp.776–777.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison
open Quasisimple Quasisimple.Hall Quasisimple.Classification Overcomponent.EmbeddingProof
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}

/-- The point and line conjugate-generated components coincide on the original
chosen flag, under only the retained earlier-source inputs. -/
theorem ofFlag_eq_of_positive_source
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
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K := by
  by_contra hne
  obtain he | ⟨hb,hm⟩ := ofFlag_eq_or_nonlinear_omega_block S f X z H h hlinear h1132
    hcent hline hXR e hpositive hradical
  · exact hne he
  have hs := ofFlag_point_mem_LStar_of_normalized_source S f X z H h hne hlinear h1132 e hcent
    (fun _ hJ _ D' => D'.source325_of_many hJ S.many) hpositive
  let := ofFlag_point_quasisimple_of_maximal S f X z H h hlinear h1132 hcent hline hXR e hne hs
  have hlt := ofFlag_nonlinear_line_lt_radicalOmega S f X z H h hne hs hlinear h1132
    hcent hline hXR e hm
  exact hlt.ne hb.2.2.2.1

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison
