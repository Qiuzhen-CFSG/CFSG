module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Fitting.Standing
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Envelope
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Fitting
public import Theory.GroupTheory.GeneralizedFitting.SylowNormalizedComponent

/-!
# Original source residuals, Fitting center and component orbits

The unchanged local setup supplies all standing data for 13.8.12(2).
Applying the genuine universal 13.3.9 input yields its residual alternatives.
The solvable Fitting envelope and the preceding 13.8.13 exclusion identify
this intersection residual with the whole Fitting residual, proving 13.8.14.
The actual cubic quotient orders make F(H/O2(H)) equal to the center of its
two-residual and show that every actual component image is quasisimple.

An ordinary component now has at most two conjugates: three would violate
the odd-rank bound inherited from the original involution centralizer.
Lifting this alternative through O2(H) supplies the orbit input for 13.8.12(1),
so no separate component-orbit classification premise is needed. The final
existence theorem chooses an actual outside component with quasisimple image.

The still independent earlier inputs are universal 13.3.9 and the solvable
exclusion 13.8.13. Relative component normality in H and the model list of
13.8.16--17 are not asserted here.
Source: Aschbacher--Smith, 13.8.12--15, printed pp.950--952.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.LocalFitting
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
 {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
 (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
 (hH : H∈Source.Hz (one L T V₁) T G₁ M)
 (hsource : SolvableExclusion.Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
include d hH hsource

theorem intersection_residual :
    SolvableExclusion.ResidualAlternative L (one L T V₁) (plus L T V₁)
      (SolvableExclusion.residualInM H M) := by
  obtain ⟨z,a⟩ := residual_local_data d hH
  exact SolvableExclusion.Residual.residual_alternative a hsource

variable (hex : ∀ J:Subgroup G, one L T V₁⊔(T:Subgroup G)≤J → J≤G₁ →
  Group.IsSolvable J → J≤M)
include hex

theorem whole_residual :
    Components.Fitting.ResidualAlternatives H L (one L T V₁) (plus L T V₁) := by
  have hFM : SolvableExclusion.twoFitting H ≤ M := le_sup_left.trans
    (hex (SolvableExclusion.twoFitting H ⊔ (one L T V₁ ⊔ (T:Subgroup G))) le_sup_right
      ((sup_le (SolvableExclusion.twoFitting_le H) hH.1.2).trans hH.2.1)
      (SolvableExclusion.twoFitting_sup_solvable hH.1.2 (local_solvable d)))
  have hr := intersection_residual d hH hsource
  rw [SolvableExclusion.residualInM_eq_of_twoFitting_le hFM] at hr
  have he : SolvableExclusion.residualWhole H = Components.Fitting.twoFittingResidual H := by
    unfold SolvableExclusion.residualWhole SolvableExclusion.twoResidual SolvableExclusion.twoFitting
      Components.Fitting.twoFittingResidual Components.Fitting.twoFittingResidualIn
    exact (map_embedded_pResidual 2 (SolvableExclusion.twoFittingIn H) H.subtype).symm
  rw [he] at hr
  rcases hr with hb | ⟨hm,heq⟩ | ⟨hm,heq⟩
  · exact Or.inl hb
  · exact Or.inr (Or.inl ⟨hm,heq⟩)
  · exact Or.inr (Or.inr ⟨⟨hm.1.toIsPerfect,hm.2⟩,heq⟩)

theorem fitting_center :
    fittingSubgroup (Source.Hstar H) =
      (center (pResidual 2 (Source.Hstar H))).map (pResidual 2 (Source.Hstar H)).subtype := by
  apply Components.Fitting.fitting_star_eq_center_twoResidual H L (one L T V₁) (plus L T V₁)
    (whole_residual d hH hsource hex) (ordinary_core_card d)
  intro hc
  exact covered_core_card d ⟨local_quotient_quasisimple d,hc.2⟩

theorem component_fitting (K:Subgroup G) (hK:(K.subgroupOf H).IsCComponent) :
    fittingSubgroup (Source.Hstar H) ≤ centralizer (Source.starImage H K:Set (Source.Hstar H)) ∧
      IsQuasisimple (Source.starImage H K) := by
  have hc := Components.Fitting.fitting_star_le_component_centralizer H L (one L T V₁) (plus L T V₁) K
    (whole_residual d hH hsource hex) (ordinary_core_card d)
    (fun hm=>covered_core_card d ⟨local_quotient_quasisimple d,hm.2⟩) hK
  exact ⟨hc,Components.star_quasisimple_of_fitting_centralizes H K hK hc⟩

omit hsource hex in
theorem star_odd_rank : IsStronglyQuasithin (Source.Hstar H) := by
  obtain ⟨z,hz,_,_,_,hG⟩ := line_involution d
  have hHc : H ≤ centralizer ({z}:Set G) := hH.2.1.trans hG
  have hr : IsStronglyQuasithin H :=
    (d.counterexample.qtke.toIsQTKE.involution_centralizer_stronglyQuasithin hz).of_injective
      (inclusion hHc) (inclusion_injective hHc)
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans (hr p hp ho)

theorem component_orbit (K:Subgroup G) (hK:(K.subgroupOf H).IsCComponent) :
    (K.subgroupOf H).Normal ∨ (normalizer (K.subgroupOf H:Set H)).index = 2 := by
  have hqs := (component_fitting d hH hsource hex K hK).2
  have hcomp : IsComponent (Source.Hstar H) (Source.starImage H K) :=
    ⟨(Components.starImage_isCComponent H K hK).subnormal,hqs⟩
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  exact cComponent_normal_or_index_two_of_quotient hK (pCore 2 H)
    (hcomp.normal_or_index_two_of_odd_rank_le_two (star_odd_rank d hH))

theorem source_component (K:Subgroup G) (hKH:K≤H) (hK:(K.subgroupOf H).IsCComponent) :
    ¬K≤M ∧ ((K⊔(T:Subgroup G))⊔one L T V₁)∈Source.Hz (one L T V₁) T G₁ M ∧
      H≤normalizer (conjugateSpanBy K (T:Subgroup G):Set G) ∧
      IsQuasisimple (Source.starImage H K) ∧
      (((conjugateSpanBy K (T:Subgroup G)⊔(one L T V₁⊔(T:Subgroup G))):Subgroup G):Set G)=
        (conjugateSpanBy K (T:Subgroup G):Set G)*(one L T V₁:Set G)*(T:Set G) := by
  obtain ⟨z,a⟩ := residual_local_data d hH
  have ho := component_orbit d hH hsource hex K hK
  obtain ⟨hout,hmem,hn,_⟩ := SolvableExclusion.Residual.component_overgroup a hsource K hKH hK ho
  exact ⟨hout,hmem,hn,(component_fitting d hH hsource hex K hK).2,
    Components.Fitting.component_orbit_product H K (one L T V₁) T hKH
      (le_sup_left.trans hH.1.2) (residual_isPPerfect _) (T_normalizes_one L T V₁ d.line_stable) ho⟩

theorem exists_source_component : ∃K:Subgroup G, K≤H ∧ (K.subgroupOf H).IsCComponent ∧
    ¬K≤M ∧ IsQuasisimple (Source.starImage H K) := by
  obtain ⟨K,hKH,hK⟩ := Components.exists_component_of_mem_Hz (one L T V₁) T G₁ M H hH hex
  exact ⟨K,hKH,hK,(source_component d hH hsource hex K hKH hK).1,
    (component_fitting d hH hsource hex K hK).2⟩

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.LocalFitting
