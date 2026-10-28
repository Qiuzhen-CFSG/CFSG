module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.BorelSource
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Solvable.Original
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.Theta

/-!
# The Suzuki Borel argument on the original A₆ configuration

The original maximal-local hypothesis supplies the exact theta identity
for H ∩ M. The natural flag gives the exponent-three quotient of L₁,
and the source solvable-overgroup theorem supplies 13.8.13. The Fitting
calculation gives quasisimplicity and the two-element component-orbit bound.
These facts construct every input to the invariant Borel argument, both
when K is T-invariant and when T exchanges two components.

Thus L₁* centralizes the actual K₀*, is normal in H*, and has order
2^r 3^s. The remaining inputs are the original earlier F.9 applicability,
13.5.4 and 13.3.9 assertions, and the reduction H = K₀L₁T. No Borel,
theta, orbit-bound or centralization assertion is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.16, printed pp.952–953; 13.7.3(9), printed p.936.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.BorelSource
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
  (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
  (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
  (hsource : SolvableExclusion.Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
  (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (one L T V₁ ⊔ (T : Subgroup G)) = H)
  {m : ℕ} (hm : 0 < m)
  (eK : (K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)

private noncomputable def originalEarlier : Earlier H K (one L T V₁) T G₁ M m := by
  let dn := localNaturalSetup d
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hH.1.2
  have hex := SolvableSource.solvable_overgroup_source d h hF9all hcentral hcomm hsource
  refine {
    parameter_pos := hm
    component_le := hKH
    component := hK
    star_quasisimple := (LocalFitting.component_fitting d hH hsource hex K hK).2
    model := eK
    base_le := hH.1.2
    overgroup_le := hH.2.1
    sylow := T.subtype hTH
    sylow_eq := ?_
    sylow_le_M := d.local_normalizer ▸ d.normalizes_L
    generated := hgen.symm
    component_index := ?_
    theta_eq := ?_
    three_quotient := ?_
    solvable_exclusion := hex }
  · rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH]
  · rcases LocalFitting.component_orbit d hH hsource hex K hK with hn | hi
    · let := hn
      simp only [normalizer_eq_top, index_top]
      decide
    · omega
  · exact (Section07.ModelExclusions.theta_intersection dn h hH).symm
  · intro x
    exact ⟨1, by simpa using Section07.ModelExclusions.point_residual_quotient_cube dn x⟩

include d h hF9all hcentral hcomm hsource hH hKH hK hgen hm eK in
/-- The Borel argument on the original configuration, with all its local
group-theoretic premises derived from earlier source theorems. -/
theorem original_group_action :
    Source.starImage H (one L T V₁) ≤
      centralizer (Source.starImage H (conjugateSpanBy K (T : Subgroup G)) : Set _) ∧
    (Source.starImage H (one L T V₁)).Normal ∧
    ∃ r s : ℕ, Nat.card (Source.starImage H (one L T V₁)) = 2 ^ r * 3 ^ s :=
  source_group_action (originalEarlier d h hF9all hcentral hcomm hsource hH hKH hK hgen hm eK)

end CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.BorelSource
