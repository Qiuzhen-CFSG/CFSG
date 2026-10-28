module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.Projection
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.OrbitClosure.ProjectionEnvelope
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.OrbitClosure.TwoFactors
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.OrbitClosure.Models
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.OrbitClosure.SourceSetup
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.Geometry

/-!
# Collapsing the component orbit with contained offenders

After (k), the exact universal 1.2.1(3) alternative bounds a nonnormal
component orbit by two and identifies its intrinsic quotient. The existing
intrinsic model theorems make that quotient centerless. The two projections
of Y₀* then generate an invariant solvable cubic envelope with order divisible
by nine, contradicting the actual Y₀/O₂(Y₀) of order three.

This adapts the lower OrbitClosure proofs to `Input`; neither generation
of the first actor by components nor best status of whole endpoints is
needed. The only additional local premise here is (k), explicitly retained
for the assembly owner. The universal orbit theorem is the exact earlier
appendix implication and is also explicit. The resulting H = LT and
relative normality feed EndpointConstruction and LateActor.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.504 and 1144, Proposition 1.2.1(3) and proof of 15.3.49(l).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels
open Subgroup Theory.GroupTheory ComponentReduction ModelReduction BinaryModels
open BinaryModels.OrbitClosure CFSG.Quasithin.Chapter1
open scoped IsMulCommutative
universe u
variable {G D : Type*} [Group G] [Group D]
private theorem map_span (L T : Subgroup G) (f : G →* D) :
    (conjugateSpanBy L T).map f = conjugateSpanBy (L.map f) (T.map f) := by
  unfold conjugateSpanBy
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨t, ht, l, hl, rfl⟩, rfl⟩
    exact ⟨f t, mem_map_of_mem f ht, f l, mem_map_of_mem f hl, by simp⟩
  · rintro ⟨_, ⟨t, ht, rfl⟩, _, ⟨l, hl, rfl⟩, rfl⟩
    exact ⟨t * l * t⁻¹, ⟨t, ht, l, hl, rfl⟩, by simp⟩

namespace Input
variable {G : Type u} [Group G] [Finite G]
    {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z E L upper : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : Input κ H M Y V Y0 T ZS Z E L upper)
include d

omit [Finite G] in
/-- Relative normality collapses the T-conjugate span. -/
theorem closure_eq_of_normal (hn : (L.subgroupOf H).Normal) : localSpan L T = L := by
  have hTH : T ≤ H := (isSylowIn_iff.mp d.sylowIn).2.1
  exact le_antisymm (conjugateSpanBy_le le_rfl
    (hTH.trans ((normal_subgroupOf_iff_le_normalizer d.l_le).mp hn)))
    (le_conjugateSpanBy L T)

/-- Once the orbit has collapsed, normality is relative to the replacement H. -/
theorem normal_and_normalized_of_closure_eq (he : localSpan L T = L) :
    (L.subgroupOf H).Normal ∧ T ≤ normalizer (L : Set G) := by
  have hn := componentClosure_normal_in_replacement L Y0 T
    (le_normalizer_iff_commutator_le_left.mpr d.component.commutator_eq.ge) d.normalizes
  rw [← d.replacement, he] at hn
  exact ⟨hn, he ▸ le_normalizer_conjugateSpanBy L T⟩

/-- A nontrivial orbit has the exact four-model quotient alternative and index two.
The intrinsic quotient is transported by its actual multiplicative equivalence. -/
theorem nonnormal_alternative (earlier : EarlierOrbitAlternative κ)
    (hne : localSpan L T ≠ L) :
    (normalizer (L.subgroupOf H : Set H)).index = 2 ∧
      Section02.NonnormalCComponentModel (L ⧸ pCore 2 L) := by
  rcases Section02.proposition_1_2_1_three_index_of_A_3_8 earlier
    d.quotient_sqtk d.component_in_H with hn | ⟨hi, hm⟩
  · exact (hne (d.closure_eq_of_normal hn)).elim
  · let e := subgroupOfEquivOfLe d.l_le
    let eqv := QuotientGroup.congr (pCore 2 (L.subgroupOf H)) (pCore 2 L) e
      (pCore_map_iso 2 e)
    exact ⟨hi, hm.of_mulEquiv eqv.symm⟩
omit [Finite G] in
theorem star_containment (hYL0 : Y0 ≤ localSpan L T) : starImage H Y0 ≤
    conjugateSpanBy (starImage H L) (starImage H T) := by
  have hTH : T ≤ H := (isSylowIn_iff.mp d.sylowIn).2.1
  have hYH : Y0 ≤ H := (d.placed.theta_eq ▸ theta_le _).trans inf_le_right
  have hY' : Y0.subgroupOf H ≤ conjugateSpanBy (L.subgroupOf H) (T.subgroupOf H) := by
    apply (map_le_map_iff_of_injective H.subtype_injective).mp
    rw [map_span, map_subgroupOf_eq_of_le d.l_le,
      map_subgroupOf_eq_of_le hTH, map_subgroupOf_eq_of_le hYH]
    exact hYL0
  have he := map_mono (f := QuotientGroup.mk' (pCore 2 H)) hY'
  rw [map_span] at he
  exact he

omit [Finite G] in
theorem star_normalizes : starImage H T ≤
    normalizer (starImage H Y0 : Set (H ⧸ pCore 2 H)) := by
  have hTH : T ≤ H := (isSylowIn_iff.mp d.sylowIn).2.1
  have hYH : Y0 ≤ H := (d.placed.theta_eq ▸ theta_le _).trans inf_le_right
  apply le_normalizer_iff_commutator_le_left.mpr
  rw [← starImage_commutator H Y0 T hYH hTH]
  exact map_mono (comap_mono (le_normalizer_iff_commutator_le_left.mp d.normalizes))

omit [Finite G] in
theorem star_commutator : starImage H L = ⁅starImage H L, starImage H Y0⁆ := by
  have hYH : Y0 ≤ H := (d.placed.theta_eq ▸ theta_le _).trans inf_le_right
  rw [← starImage_commutator H L Y0 d.l_le hYH, ← d.component.commutator_eq]

theorem star_moves (hne : localSpan L T ≠ L) :
    ¬ starImage H T ≤ normalizer (starImage H L : Set (H ⧸ pCore 2 H)) := by
  intro hn
  let _ := pCore_isNilpotent (p := 2) (G := H)
  have hi : T.subgroupOf H ≤ normalizer (L.subgroupOf H : Set H) := by
    have h := map_le_iff_le_comap.mp hn
    unfold starImage at h
    rwa [normalizer_cComponent_quotient d.component_in_H (pCore 2 H)] at h
  have ht : T ≤ normalizer (L : Set G) := by
    have h := (map_mono (f := H.subtype) hi).trans ((L.subgroupOf H).le_normalizer_map H.subtype)
    rwa [map_subgroupOf_eq_of_le d.l_le,
      map_subgroupOf_eq_of_le (isSylowIn_iff.mp d.sylowIn).2.1] at h
  exact hne (le_antisymm (conjugateSpanBy_le le_rfl ht) (le_conjugateSpanBy L T))

omit [Finite G] in
theorem star_theta : theta (starImage H Y0) = starImage H Y0 := by
  have hYH : Y0 ≤ H := (d.placed.theta_eq ▸ theta_le _).trans inf_le_right
  have ht : theta (Y0.subgroupOf H) = Y0.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [theta_map_of_injective _ H.subtype_injective,
      map_subgroupOf_eq_of_le hYH, ← d.placed.theta_eq, theta_idempotent]
  apply le_antisymm (theta_le _) _
  have hh := theta_map_le (Y0.subgroupOf H) (QuotientGroup.mk' (pCore 2 H))
  rwa [ht] at hh

theorem star_solvable : Group.IsSolvable (starImage H Y0) := by
  have hYH : Y0 ≤ H := (d.placed.theta_eq ▸ theta_le _).trans inf_le_right
  let _ := d.y_solvable
  let _ : Group.IsSolvable (Y0.subgroupOf H) := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hYH).toMonoidHom) (subgroupOfEquivOfLe hYH).injective
  exact Group.isSolvable_of_surjective ((QuotientGroup.mk' (pCore 2 H)).subgroupMap_surjective (Y0.subgroupOf H))

/-- The orbit itself constructs the invariant solvable cubic envelope forbidden by (j). -/
theorem no_two_orbit (hYL0 : Y0 ≤ localSpan L T) (hne : localSpan L T ≠ L)
    (hi : (normalizer (L.subgroupOf H : Set H)).index = 2)
    (hz : center (L ⧸ pCore 2 L) = ⊥) : False := by
  let _ := d.intrinsic_quasisimple
  let D := H ⧸ pCore 2 H
  let B := starImage H L
  let Ys := starImage H Y0
  let Ts := starImage H T
  let S := starImage H (Y0 ⊔ T)
  let e := componentStarEquiv H L d.l_le d.component_in_H
  let : IsQuasisimple B := starImage_quasisimple H L d.l_le d.component_in_H
  let := pCore_isNilpotent (p := 2) (G := H)
  have hB : IsComponent D B :=
    ⟨(d.component_in_H.map_quotient (pCore 2 H)).subnormal, inferInstance⟩
  have hZ : center B = ⊥ := by
    apply eq_bot_of_card_eq
    rw [← Nat.card_congr (centerCongr e).toEquiv, hz, card_bot]
  have hiB : (normalizer (B : Set D)).index = 2 :=
    (cComponent_normalizer_index_quotient d.component_in_H (pCore 2 H)).trans hi
  obtain ⟨C, hd, hc, hY, hb, hcne, hcg, hpair⟩ := pair_of_two_orbit B Ys Ts
    hB hZ hiB (star_moves d hne) (star_containment d hYL0) (star_normalizes d) (star_commutator d)
  have hYn : S ≤ normalizer (Ys : Set D) := by
    have hYH : Y0 ≤ H := (d.placed.theta_eq ▸ theta_le _).trans inf_le_right
    have hTH : T ≤ H := (isSylowIn_iff.mp d.sylowIn).2.1
    apply le_normalizer_iff_commutator_le_left.mpr
    rw [← starImage_commutator H Y0 (Y0 ⊔ T) hYH (sup_le hYH hTH)]
    exact map_mono (comap_mono (le_normalizer_iff_commutator_le_left.mp
      (sup_le Y0.le_normalizer d.normalizes)))
  let : Group.IsSolvable Ys := star_solvable d
  obtain ⟨hsol, ht, hn, hdiv⟩ := projectionEnvelope_properties B C Ys S
    hd hc hY (star_theta d) hb hcne (star_commutator d) hcg hYn (fun s _ => hpair s)
  let := hsol
  exact d.no_cubic_envelope
    (projectionEnvelope B C Ys) ht hn hdiv


/-- Conditional orbit assembly: the containment (k) remains an explicit
premise, while closure equality is proved from the universal orbit theorem. -/
theorem closure_eq (earlier : EarlierOrbitAlternative κ)
    (hYL0 : Y0 ≤ localSpan L T) : localSpan L T = L := by
  let := d.intrinsic_quasisimple
  by_contra hn
  obtain ⟨hi, hm⟩ := d.nonnormal_alternative earlier hn
  exact d.no_two_orbit hYL0 hn hi (nonnormal_model_center_eq_bot hm)

/-- The exact generation and relative normality required at the late endpoint. -/
theorem reduced_structure (earlier : EarlierOrbitAlternative κ)
    (hYL0 : Y0 ≤ localSpan L T) :
    localSpan L T = L ∧ Y0 ≤ L ∧ H = L ⊔ T ∧
      (L.subgroupOf H).Normal ∧ H ≤ normalizer (L : Set G) ∧
      IsSylowIn 2 (T ⊓ L) L ∧
      IsSylowIn 2 (starImage H (T ⊓ L)) (starImage H L) := by
  have he := d.closure_eq earlier hYL0
  have hy : Y0 ≤ L := he ▸ hYL0
  have hn := (d.normal_and_normalized_of_closure_eq he).1
  have hg : H = L ⊔ T := by
    simpa only [reducedOvergroup, he, ← sup_assoc, sup_eq_left.mpr hy] using d.replacement
  exact ⟨he, hy, hg, hn, (normal_subgroupOf_iff_le_normalizer d.l_le).mp hn,
    component_inter_sylow H T L d.sylowIn d.l_le d.component_in_H⟩

/-- The established reduction feeds the existing binary-generation and
point-case language without constructing the stronger LocalControl record. -/
theorem reduced_data (earlier : EarlierOrbitAlternative κ)
    (hYL0 : Y0 ≤ localSpan L T) : ModelExclusions.ReducedLocalData H M L Y0 T := by
  obtain ⟨_, hy, hg, _, hn, _, _⟩ := d.reduced_structure earlier hYL0
  refine ⟨?_, hy, d.placed.theta_eq.symm, d.sylowIn, d.placed.t_le_m,
    hn, d.minimal.outside, ?_⟩
  · simpa only [sup_eq_left.mpr hy] using hg
  · intro K hb hK hs
    exact d.overgroups K hs hb hK

end Input
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels
