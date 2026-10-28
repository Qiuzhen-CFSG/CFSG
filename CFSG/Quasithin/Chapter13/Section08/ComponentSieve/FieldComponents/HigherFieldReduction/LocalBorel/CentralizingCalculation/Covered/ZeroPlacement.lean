module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Covered.ZeroPlacement.Reduction
public import Theory.GroupTheory.PResidual.NormalityLift

/-!
# Conditional assembly of the covered central-direction placement

The earlier bound N_G(L₀) ≤ M excludes normalization of L₀* by K*:
H = KL₁T would make L₀* normal in H*, and two-perfectness lifts that
normality through O₂(H) ≤ T to H ≤ N_G(L₀), contrary to H ≰ M.

Combining this exclusion with the marked intersection reduction proves
L₀ ≤ BX provided the remaining higher-field model calculation shows that
O²(L₁ ∩ BX) = X forces K* to normalize L₀*. That model calculation is
still an explicit obligation; no unconditional placement or B_C identity
is claimed in this module.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.2.2(3),(9), printed pp.877–878; 13.7.3(9), p.936;
the calculation in 13.8.20, printed p.954/PDF p.971.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Covered.ZeroPlacement
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open LocalAction
universe u v
variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {H K L V V₁ V₂ V₃ M G₁ : Subgroup G}
  [(Source.starImage H K).Normal] {n : ℕ} {unitary four : Bool}
  (d : SourceContext.{u,v} T H K L V V₁ V₂ V₃ M G₁ n unitary four)
  (a : NaturalSetup L (T : Subgroup G) V V₁ V₃)
  (hfactor : one L (T : Subgroup G) V₁ = plus L (T : Subgroup G) V₁ ⊔ zero L)

include d hfactor in
/-- If K* normalized the central mark, generation would make that mark normal
in H*. The two-perfect normality lift would contradict the earlier bound on
N_G(L₀). -/
theorem not_zero_star_normalizing
    (hNM : normalizer (zero L : Set G) ≤ M) :
    ¬ Source.starImage H K ≤
      normalizer (Source.starImage H (zero L) : Set (Source.Hstar H)) := by
  intro hK
  let Z := zero L
  have hZH : Z ≤ H :=
    (zero_le_one_of_factorization L (T : Subgroup G) V₁ hfactor).trans d.one_le_H
  have hTZ : (T : Subgroup G) ≤ normalizer (Z : Set G) :=
    d.standing.normalizes_L.trans (normalizer_le_zero_normalizer L)
  have hDZ : one L (T : Subgroup G) V₁ ≤ normalizer (Z : Set G) :=
    one_normalizes_zero L (T : Subgroup G) V₁ d.standing.normalizes_L
  have hgen : Source.starImage H K ⊔
      Source.starImage H (one L (T : Subgroup G) V₁) ⊔
      Source.starImage H (T : Subgroup G) = ⊤ := by
    rw [← star_sup H K _ d.component_le d.one_le_H,
      ← star_sup H _ _ (sup_le d.component_le d.one_le_H) d.T_le_H,
      ← d.generated]
    simp only [Source.starImage, subgroupOf_self,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  let : (Source.starImage H Z).Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen]
    exact sup_le (sup_le hK (starImage_normalizes H _ Z hDZ))
      (starImage_normalizes H _ Z hTZ)
  let A := Z.subgroupOf H
  let q := QuotientGroup.mk' (pCore 2 H)
  have hA : IsPPerfect 2 A := (residual_isPPerfect (centralPreimage L)).of_surjective
    (subgroupOfEquivOfLe hZH).symm.toMonoidHom (subgroupOfEquivOfLe hZH).symm.surjective
  have hQZ : q.ker ≤ normalizer (A : Set H) := by
    rw [QuotientGroup.ker_mk', ← subgroupOf_normalizer_eq hZH]
    obtain ⟨S, hS⟩ := d.sylow_H
    intro x hx
    apply hTZ
    rw [← hS]
    exact mem_map_of_mem H.subtype (pCore_isPGroup.le_sylow_of_normal S hx)
  let : (A.map q).Normal := inferInstanceAs (Source.starImage H Z).Normal
  have hnA : A.Normal := normal_of_map_normal_of_pPerfect q A hA
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) hQZ
  let := hnA
  exact d.member.2.2 ((le_normalizer_of_normal_subgroupOf hZH).trans hNM)

include a hfactor in
/-- Conditional assembly. The remaining model calculation must normalize the
central mark in the degenerate intersection branch; it is not asserted here. -/
theorem zero_le_product_of_degenerate_action
    (hNM : normalizer (zero L : Set G) ≤ M)
    (hdegenerate : residual (one L (T : Subgroup G) V₁ ⊓
        (d.B ⊔ plus L (T : Subgroup G) V₁)) = plus L (T : Subgroup G) V₁ →
      Source.starImage H K ≤
        normalizer (Source.starImage H (zero L) : Set (Source.Hstar H))) :
    zero L ≤ d.B ⊔ plus L (T : Subgroup G) V₁ := by
  by_contra hz
  exact not_zero_star_normalizing d hfactor hNM
    (hdegenerate (source_intersection_residual_of_not_zero d a hfactor hz))

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Covered.ZeroPlacement
