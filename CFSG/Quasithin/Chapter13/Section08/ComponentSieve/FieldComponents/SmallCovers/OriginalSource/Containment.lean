module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource.Residual
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics.MarkedMathieu
public import Theory.GroupTheory.CComponent.TripleMathieuTheta


/-!
# The original Mathieu triple-cover reduction to a six-cover

The order-three normalizer theorem places all original theta generators
in K, proving L₁ ≤ K. The preceding central-residual argument gives
Y < L₁, and the original reduced generation gives H = KT. These facts
construct the complete input to the native marked Mathieu replacement.

Its hexad C-component K₁ is strictly smaller than K, contains L₁, and
lies outside M. Transfer the strongly quasithin and K-group conditions
from H to K₁T, retain the literal Sylow and theta data, and identify the
new intrinsic quotient with the actual triple-A₆ carrier. This constructs
a new SourceContext on K₁T and K₁, including its catalogue entry.

Thus the Mathieu triple-cover row is excluded once the six-cover branch
is excluded for these original contexts. That branch remains with the
field-sieve owner qt-d-138-fields-source; the original section owner
qt-d-1381-source supplies the earlier local context. The terminal
six-cover argument must still use the literal V_H/U_H permutation section.
Source: Aschbacher–Smith, 13.8.21(2), printed p.956 (PDF p.973),
with A.3.18, pp.51–52.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource
open Reduction Reduction.LocalGeometry Reduction.LocalGeometry.CoverParabolics
open SourceCompletion LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

private theorem component_le (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K) : K ≤ H :=
  (le_sup_left.trans le_sup_left).trans_eq c.component.generated

/-- A.3.18 puts every original theta generator in the actual Mathieu cover. -/
theorem source_mathieu_cover_containment
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (eK : (K ⧸ pCore 2 K) ≃* Components.Models.M22Triple) : one L T V₁ ≤ K := by
  let D := K.subgroupOf H
  let := c.component.normal
  let e := (QuotientGroup.congr (pCore 2 D) (pCore 2 K)
    (subgroupOfEquivOfLe (component_le c)) (pCore_map_iso 2 _)).trans eK
  rw [c.component.theta, Subgroup.closure_le]
  intro x hx
  let y : H := ⟨x,hx.1.1⟩
  exact TripleMathieuTheta.order_three_mem D c.component.component e
    (c.component.sqtk.stronglyQuasithin 3 Nat.prime_three (by decide))
    ((H.orderOf_coe y).symm.trans hx.2) (le_normalizer_of_normal (mem_top y))

/-- The complete earlier-source input to the native marked Mathieu replacement.
Containment, product generation and the proper residual are proved here. -/
theorem source_mathieu_cover_markedSetup
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (eK : (K ⧸ pCore 2 K) ≃* Components.Models.M22Triple) :
    MarkedSetup H K (one L T V₁) T G₁ M := by
  have hle := source_mathieu_cover_containment c eK
  have hH := c.component.local_overgroup
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hH.1.2
  have hc : Nat.card (center (K ⧸ pCore 2 K)) = 3 :=
    (Nat.card_congr (centerCongr eK).toEquiv).trans Components.CoverModels.m22Triple_center_card
  let := LocalFitting.local_solvable c.localSetup
  have hlT : one L T V₁ ≤ one L T V₁ ⊔ (T : Subgroup G) := le_sup_left
  exact {
    mem_Hz := hH
    component_le := component_le c
    component := c.component.component
    component_normal := c.component.normal
    sylow := ⟨T.subtype hTH,map_subgroupOf_eq_of_le hTH⟩
    sylow_le_M := by rw [c.localSetup.local_normalizer]; exact c.localSetup.normalizes_L
    generated := by rw [←c.component.generated,sup_eq_left.mpr hle]
    seed_le_component := hle
    seed_solvable := Group.isSolvable_of_isSolvable_injective (inclusion_injective hlT)
    theta := c.component.theta
    proper_residual := lt_of_le_of_ne (source_residual_located c hc).2
      (source_mathieu_cover_residual_ne_one c eK)
    quasisimple := IsQuasisimple.of_mulEquiv eK.symm
    center_card := hc
    solvable_overgroups := SolvableSource.solvable_overgroup_source c.localSetup c.maximal c.f9
      c.centralizer c.noncentral_core c.earlier1339 }

private noncomputable def mathieuCentralEquiv
    (eK : (K ⧸ pCore 2 K) ≃* Components.Models.M22Triple) :
    (K ⧸ (pCore 2 K).centralPreimage) ≃* Sporadic.Mathieu.M22 :=
  (centralPreimageQuotientEquiv (pCore 2 K)).trans
    ((QuotientGroup.congr _ _ eK (by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        exact (centerCongr eK ⟨y,hy⟩).property
      · intro hx
        exact ⟨eK.symm x,(centerCongr eK.symm ⟨x,hx⟩).property,eK.apply_symm_apply x⟩)).trans
      Components.CoverModels.m22Triple_quotientCenterEquiv)

/-- The actual local hexad component yields a strictly smaller six-cover
source context with the same local A₆ data and the literal restricted theta.
This discharges every premise of the marked Mathieu replacement. -/
theorem source_mathieu_cover_replacement_context
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (eK : (K ⧸ pCore 2 K) ≃* Components.Models.M22Triple) :
    ∃ w : LocalSix K T, w.subgroup < K ∧
      Nonempty ((w.subgroup ⧸ pCore 2 w.subgroup) ≃* Components.Models.A6Triple) ∧
      Nonempty (SourceContext T L V V₁ V₂ V₃ M G₁
        (w.subgroup ⊔ (T : Subgroup G)) w.subgroup) ∧
      coverResidualIn w.subgroup < one L T V₁ ∧
      (w.subgroup ⊔ (T : Subgroup G)) ⊓ M < w.subgroup ⊔ (T : Subgroup G) := by
  let s := source_mathieu_cover_markedSetup c eK
  obtain ⟨B,hB,hn,hL,hout,hres,w,hw,hlt,hcover,s',hproper⟩ :=
    MarkedMathieu.exists_marked_replacement s (mathieuCentralEquiv eK)
  obtain ⟨e⟩ := Components.CoverModels.a6Triple_nonempty_mulEquiv
    ⟨hcover.1,⟨mulEquivOfPrimeCardEq hcover.2.1 (Nat.card_zmod 3)⟩,hcover.2.2⟩
  have hH' : w.subgroup ⊔ (T : Subgroup G) ≤ H :=
    sup_le (hlt.le.trans (component_le c))
      (le_sup_right.trans c.component.local_overgroup.1.2)
  refine ⟨w,hlt,⟨e⟩,⟨?c'⟩,s'.proper_residual,hproper⟩
  exact {
    localSetup := c.localSetup
    maximal := c.maximal
    f9 := c.f9
    centralizer := c.centralizer
    noncentral_core := c.noncentral_core
    earlier1339 := c.earlier1339
    component := {
      sqtk := (IsSQTK.equiv (subgroupOfEquivOfLe hH')).mp
        (c.component.sqtk.subgroup ((w.subgroup ⊔ (T : Subgroup G)).subgroupOf H))
      local_overgroup := s'.mem_Hz
      generated := by rw [sup_eq_left.mpr s'.seed_le_component]
      component := s'.component
      normal := s'.component_normal
      external := by simpa only [hw] using hout
      theta := s'.theta }
    catalogue := .alternating_six_cover ⟨e⟩ }

/-- Once the six-cover source branch is excluded, the actual replacement
excludes the Mathieu triple cover in either local quotient case. The common
field-sieve owner retains that single six-cover exclusion obligation. -/
theorem source_no_mathieu_cover_of_six_exclusion
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (hsix : ∀ (H' K' : Subgroup G), SourceContext T L V V₁ V₂ V₃ M G₁ H' K' →
      ¬ Nonempty ((K' ⧸ pCore 2 K') ≃* Components.Models.A6Triple)) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Components.Models.M22Triple) := by
  rintro ⟨eK⟩
  obtain ⟨w,_,he,⟨c'⟩,_,_⟩ := source_mathieu_cover_replacement_context c eK
  exact hsix _ _ c' he

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource
