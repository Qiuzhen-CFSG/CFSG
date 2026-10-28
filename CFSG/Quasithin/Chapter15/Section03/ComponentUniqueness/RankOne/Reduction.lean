module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.Preliminary
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.AlternatingExclusion
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.QuotientMaximality
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.SourceInputs
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.DiagonalExclusion
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.ComponentProjection
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.QuotientLocality

/-!
# Construction of the rank-one reduction

The assumed `S₃` shadow and the theta identity give the exact two-core index
three. They select 15.3.11(5ii), including the genuine residual identity and
the second choice of Hypothesis 15.3.10. This proves (a), and that choice
gives the first-plane centralization in (b). The plane-normalizer bound then
gives (c). The two standard conventions for the prime-to-three residual are
proved equivalent, and residuals are transported through the actual quotient.

`AlternatingExclusion` constructs the direct product needed for (d) from
the earlier plane and residual geometry. `QuotientStructure` proves the
two-kernel, generalized Fitting, simplicity, radical and shadow assertions
after component placement. `QuotientMaximality` lifts every competing
characteristic-two overgroup and rules it out using 15.3.25.

`reducedConfiguration_of_source` constructs the full `ReducedConfiguration`
from the earlier source inputs and the assumed S₃ shadow. The literal
15.3.11 alternatives select the residual choice; the natural action supplies
the planes and the A₄-square obstruction. The invariant Borel calculations
exclude the signed diagonal alternatives, with the actual diagonal actor
retained in the linear index-three contradiction. The constructed component
projection then gives containment, relative normality and `I = LS`. Finally
the quotient locality proof constructs every remaining clause of (e).

Only earlier source results and the explicitly authorized alternatives
(i)--(iii) are inputs. No result uses 15.3.35 or assumes the reduction output.
The model classification and the final contradiction of 15.3.43 belong to
the parent source assembly.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.43(a)--(e), printed pp.1139--1140.
-/

@[expose] public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.RankOne

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The first-plane part of (b) and all of (c), from the actual second
residual choice and the earlier plane-normalizer bound. -/
theorem first_plane_reduction {Yplus Y V₁ S M L : Subgroup G}
    (hchoice : Yplus = Stellmacher.twoResidualAmbient
      (Y ⊓ centralizer (V₁ : Set G)))
    (hV₁S : V₁ ≤ S) (hnorm : normalizer (V₁ : Set G) ≤ M)
    (hL : ¬ L ≤ M) :
    ⁅V₁, Yplus⁆ = ⊥ ∧ ⁅V₁, L⁆ ≠ ⊥ ∧
      S ⊓ centralizer (Yplus : Set G) ≠ S ⊓ centralizer (L : Set G) := by
  have hc := centralizes_first_plane_of_residual_choice hchoice
  exact ⟨hc, plane_action_and_distinct_centralizers hV₁S hc hnorm hL⟩

/-- Once the component placement is supplied, minimality constructs the
generation identity and hence the actual two-kernel and radical transport.
The remaining local-image properties are separate obligations. -/
theorem quotient_core_reduction {Yplus S M I L : Subgroup G}
    (d : ComponentAction I L)
    (hI : I ∈ minimalOutsideFamily Yplus S M)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hYL : Yplus ≤ L) (hL : ¬ L ≤ M)
    (hz : (center L).map L.subtype = L.pCoreIn 2)
    (hshadow : SymmetricThreeShadow Yplus S) :
    I = L ⊔ S ∧ IsPGroup 2 d.kernel ∧
      d.image ((Yplus ⊔ S).pCoreIn 2) = (d.image Yplus ⊔ d.image S).pCoreIn 2 ∧
      SymmetricThreeShadow (d.image Yplus) (d.image S) := by
  have hgen := eq_component_join_sylow hI P hP d.component_le hYL hL
  have hS : IsPGroup 2 S := hP ▸ P.isPGroup'.map I.subtype
  have hk := d.kernel_isTwoGroup hS hgen hz
  have hYI := hYL.trans d.component_le
  have hSI : S ≤ I := hP ▸ map_subtype_le _
  refine ⟨hgen, hk, ?_, d.image_shadow hYI hSI hk hshadow⟩
  rw [d.image_radical (sup_le hYI hSI) hk, d.image_sup hYI hSI]

/-- Construct all of 15.3.43(a)--(e) that is independent of the final
component catalogue. Every intermediate input of the four reduction
branches is discharged from the indicated earlier source results.

The alternatives are exactly (i)--(iii) at the start of 15.3.43, with
actual quotient-model equivalences and compatible diagonal actions.
In particular neither inner action nor component placement is a premise. -/
theorem reducedConfiguration_of_source (d : CharacteristicTwo.LocalData G)
    {I L : Subgroup G} (hI : I ∈ d.HplusMinimal)
    (h : ReductionSourceInputs d I L)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    (halt : Candidates.Alternatives15343 d.Yplus I L (localSpan L d.S)) :
    ReducedConfiguration d.Yplus d.S d.M I L d.V₁ d.V₂ := by
  have htheta := h.outside_structure.theta_eq.symm
  have hne : d.Yplus ≠ ⊥ := by
    intro he
    apply h.outside_structure.action_normalizer.2.2
    simp [CharacteristicTwo.LocalData.starImage, localActionImage, he]
  have h11 := preliminary_alternative_of_source d h.outside_structure.local_structure
  obtain ⟨hchoice, hres, hindex⟩ :=
    rank_one_choice_of_preliminary_alternative hshadow htheta hne h11
  have hij : (1 : OrthogonalPlaneIndex) ≠ Multiplicative.ofAdd (1 : ZMod 2) := by
    decide
  obtain ⟨hV₁S, hV₂S, helem, hcard, hcentral, hcomm, _, hMV₂, hA4⟩ :=
    PlaneGeometry.plane_reduction_of_preliminary_alternative d.action d.T d.sylow_le
      (localModule_le d.T d.sylow_le) h.characteristic_two h.residual_image
      h.residual_core h.residual_quotient h.not_alternating_square hij
      hshadow htheta hne h11
  obtain ⟨_, hNV₁, hNV₂, _⟩ := h.outside_structure.second_choice hchoice
  have hSM : d.S ≤ d.M := inf_le_left.trans d.sylow_le
  let localSetup : DiagonalExclusion.LocalSetup d.Yplus d.S d.M I L := {
    outside := hI.1
    sylow := h.outside_structure.sylow
    sylow_le := hSM
    component_le := h.component_le
    component := h.component
    component_outside := h.component_outside
    odd_core := h.outside_structure.odd_core
    orbit_bound := h.component_orbit
    theta_eq := htheta
    normalizer_eq := h.outside_structure.normalizer_eq
    local_fitting := h.outside_structure.generalized_fitting
    rank_positive := h.component_rank
    rank_overgroup := h.overgroup_rank
    characteristic_two_containment := h.invariant_subgroup
    shadow := hshadow
    residual := hres
    index := hindex }
  let planes : DiagonalExclusion.PlaneData d.Yplus d.S d.M I d.V₁ d.V₂ := {
    first_le := hV₁S
    second_le := hV₂S
    first_centralizes := hcentral
    first_normalizer := hNV₁
    second_normalizer := hNV₂
    second_elementary := helem
    second_card := hcard
    second_commutator := hcomm
    second_normalized := hMV₂
    not_alternating_four := hA4 }
  have hi := (localSetup.inner_of_alternatives d planes halt).1
  have hinner : ∀ y ∈ d.Yplus, ∃ l ∈ L, l⁻¹ * y ∈ centralizer (L : Set G) := by
    intro y hy
    have hm : y ∈ (L : Set G) * (centralizer (L : Set G) : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left L (centralizer (L : Set G))
        (Subgroup.centralizer_le_normalizer _)]
      exact hi hy
    obtain ⟨l, hl, c, hc, rfl⟩ := hm
    refine ⟨l, hl, ?_⟩
    rw [inv_mul_cancel_left]
    exact hc
  obtain ⟨P, hP⟩ := h.outside_structure.sylow
  have hSY : d.S ≤ normalizer (d.Yplus : Set G) :=
    (le_inf hSM localSetup.sylow_le_overgroup).trans localSetup.local_normalizes
  obtain ⟨_, hYL, hgen, hnorm, _⟩ :=
    ComponentProjection.containment_and_relative_normality hI P hP h.component_le
      h.component h.component_outside hSY htheta h.outside_structure.normalizer_eq
      hres hindex h.component_center hinner
  let a : ComponentAction I L := ⟨h.component_le, hnorm⟩
  have hquot := (a.quotientConditions_of_plane hI P hP hSM h.component
    h.component_center h.component_outside hYL htheta hres hshadow
    h.outside_structure.generalized_fitting hV₂S helem hcard hMV₂ hNV₂ hcomm
    h.outside_not_characteristic_two).1
  exact {
    toComponentAction := a
    minimal := hI
    sylow := ⟨P, hP⟩
    sylow_le_M := hSM
    component := h.component
    oddCore := h.outside_structure.odd_core
    component_center := h.component_center
    component_outside := h.component_outside
    generated := hgen
    y_le_component := hYL
    residual := hres
    index := hindex
    theta_eq := htheta
    normalizer_eq := h.outside_structure.normalizer_eq
    local_fitting := h.outside_structure.generalized_fitting
    shadow := hshadow
    plane_one_le := hV₁S
    plane_two_le := hV₂S
    plane_one_centralizes := hcentral
    plane_one_acts := (plane_action_and_distinct_centralizers
      hV₁S hcentral hNV₁ h.component_outside).1
    plane_two_elementary := helem
    plane_two_card := hcard
    plane_two_commutator := hcomm
    plane_two_normalized := hMV₂
    not_alternating_four := hA4
    quotient := hquot }

end CFSG.Quasithin.Chapter15.Section03.RankOne
