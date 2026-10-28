module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Nonquasisimple.Cartan.Quadratic
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Nonquasisimple.Frattini.Catalogue

/-!
# The remaining proper overcomponent in the Cartan argument

Apply the complete catalogue and Frattini calculation to the original
chosen flag. Its literal residual lies in a unique normal C-component of
N_G(R₁). If that component equals the residual, X-normalization follows
from relative normality and the existing Cartan endpoint proves Kz = K.
Otherwise the component is strictly larger, its two-core quotient is
quasisimple, and the PSL₂(p²) model is impossible by the original seed's
full-Sylow action.

The surviving proper-component classification is still required to finish
11.4.2. Fitting centralization is supplied by the canonical-star argument
in Nonquasisimple.lean; canonical stars themselves remain an obligation.
Both remaining steps and final assembly belong to
qt-d-1222-comparison-nonquasisimple. No embedding classification is assumed
or asserted by this reduction.
Source: Aschbacher--Smith, 11.4.2, printed p.777.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Cartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {E : Closure.Geometry D}

/-- The source Cartan argument now has only a proper quasisimple
containing-component branch. Both the nonquasisimple extension and the
quadratic PSL₂ branch are excluded on the original chosen flag. -/
theorem ofFlag_eq_or_proper_quasisimple_overcomponent (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H)) (hA : f.Li 0 ≠ ⊥)
    (hseed : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hn : ¬ IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz))
    (hF : fittingPreimage (ofFlag S f X z H) ≤ centralizer ((ofFlag S f X z H).V₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hXN : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G))
    (hc : LocalGeometry.Components.ComponentAlternative
      (ofFlag S f X z H).L₁ (ofFlag S f X z H).Kz S.field.degree) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K ∨
      ∃ (p : ℕ) (K₀ : Subgroup G), Source.ExceptionalPrime p ∧ S.field.degree = 2 ∧
        Source.NormalComponentIn (normalizer ((ofFlag S f X z H).R₁ : Set G)) K₀ ∧
        normalizerResidual (ofFlag S f X z H) < K₀ ∧
        IsQuasisimple (K₀ ⧸ pCore 2 K₀) ∧
        ¬ ClassicalGroup.IsPSL (K₀ ⧸ pCore 2 K₀) 2 (p ^ 2) ∧
        ClassicalGroup.IsPSL (normalizerResidual (ofFlag S f X z H) ⧸
          pCore 2 (normalizerResidual (ofFlag S f X z H))) 2 p := by
  by_cases he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K
  · exact .inl he
  obtain ⟨hs,hd,_,_,p,hp,hm,_⟩ :=
    Frattini.ofFlag_frattini_of_catalogue S f X z H h hA hseed hf he hn hF hc
  have hp3 : 3 < p := by have := hp.1.two_le; have := hp.2.1; omega
  let : Fact p.Prime := ⟨hp.1⟩
  obtain ⟨K₀,hK,hBK,_⟩ := ofFlag_exists_unique_normal_overcomponent S f X z H h hp3 hm
  by_cases heB : normalizerResidual (ofFlag S f X z H) = K₀
  · have hNK : normalizer ((ofFlag S f X z H).R₁ : Set G) ≤ normalizer (K₀ : Set G) :=
      (normal_subgroupOf_iff_le_normalizer hK.1.1).mp hK.2
    have hXB : X ≤ normalizer (normalizerResidual (ofFlag S f X z H) : Set G) :=
      heB.symm ▸ hXN.trans hNK
    exact .inl (eq_of_fitting_normalizer_split h hf hline hF hs hXB)
  · exact .inr ⟨p,K₀,hp,hd,hK,lt_of_le_of_ne hBK heB,
      ofFlag_overcomponent_quasisimple S f X z H h hp3 hm hK.1 hBK,
      ofFlag_overcomponent_not_quadratic S f X z H hseed hd hp hK.1 hBK,hm⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Cartan
