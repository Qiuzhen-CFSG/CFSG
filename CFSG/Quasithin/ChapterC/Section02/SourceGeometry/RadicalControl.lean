module

public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.StarRadical
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleRadicalNormalizer

/-!
# Placement of the original star-radical normalizer

The original C.2.3 control contains the component normalizer of J(R)*.
Normalizer lifting through O₂(KR) and the remaining odd star kernel shows
that N(R*) normalizes J(R)*. Thus N_{K*}(R*) lies in the literal marked
intersection M_K*. If R* lies in K*, this is precisely the radical-intersection
normalizer needed for the classical parabolic theorem. The proof also shows
that this intersection is nontrivial in the inner-action branch.

No containment of R* in K* is claimed in the outer-action branch. Its marked
placement remains the additional argument of Asc81b 8.9/10.5.

Source: Aschbacher--Smith C.2.7(3), printed pp.146--147.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {H K R M : Subgroup G}

theorem star_radical_normalizer_le_thompson_normalizer
    (h : Input κ H R M K) [(K.subgroupOf H).Normal] :
    normalizer (starImage K R R : Set (StarQuotient K R)) ≤
      normalizer (starImage K R (elementaryAbelianMaxJ R) : Set (StarQuotient K R)) := by
  let D := K ⊔ R
  let R₀ := R.subgroupOf D
  let q := QuotientGroup.mk' (starKernel K R)
  have hR : IsPGroup 2 R := by
    have hh := h.setup.radical.isPGroup.map H.subtype
    rwa [map_subgroupOf_eq_of_le h.setup.radical_le] at hh
  have hQR : pCore 2 D ≤ R₀ := fun x hx => source_joinCore_le_radical h
    (mem_map_of_mem D.subtype hx)
  have hcop : Nat.Coprime 2 (Nat.card (q.ker.map (QuotientGroup.mk' (pCore 2 D)))) := by
    simpa only [q, QuotientGroup.ker_mk'] using
      starKernel_core_image_coprime_of_normal_input h
  have hn := QuasisimpleThompson.normalizer_image_le_normalizer_maxJ_of_odd_core_kernel
    R₀ hR.comap_subtype q (QuotientGroup.mk'_surjective _) (pCore 2 D) hQR
    (by simpa only [q, QuotientGroup.ker_mk'] using core_le_starKernel K R) hcop
  have hJR : elementaryAbelianMaxJ R ≤ D :=
    (sSup_le fun _ hA => hA.1).trans (show R ≤ D from le_sup_right)
  have hJ : elementaryAbelianMaxJ R₀ = (elementaryAbelianMaxJ R).subgroupOf D := by
    apply map_injective D.subtype_injective
    rw [←elementaryAbelianMaxJ_map_injective D.subtype D.subtype_injective,
      map_subgroupOf_eq_of_le (show R ≤ D from le_sup_right),
      map_subgroupOf_eq_of_le hJR]
  simpa only [hJ, R₀, q, starImage] using hn

theorem star_radical_normalizer_control
    (h : Input κ H R M K) [(K.subgroupOf H).Normal] :
    starImage K R K ⊓ normalizer (starImage K R R : Set (StarQuotient K R)) ≤
      starM K R M :=
  (inf_le_inf_left _ (star_radical_normalizer_le_thompson_normalizer h)).trans
    (star_thompson_intersection_of_normal_input h).1

theorem star_radical_ne_bot
    (h : Input κ H R M K) [(K.subgroupOf H).Normal] :
    starImage K R R ≠ ⊥ := by
  intro he
  have hker : R.subgroupOf (K ⊔ R) ≤ starKernel K R := by
    have hh := (map_eq_bot_iff (R.subgroupOf (K ⊔ R))).mp he
    simpa only [QuotientGroup.ker_mk'] using hh
  exact thompson_not_le_starKernel_of_normal_input h
    ((sSup_le fun _ hA => hA.1).trans hker)

theorem star_intersection_radical_of_inner
    (h : Input κ H R M K) [(K.subgroupOf H).Normal]
    (hinner : starImage K R R ≤ starImage K R K) :
    IsPRadical 2 ((starImage K R R).subgroupOf (starImage K R K)) := by
  apply star_intersection_radical_of_normal_input h
  intro he
  apply star_radical_ne_bot h
  have hm := congrArg (map (starImage K R K).subtype) he
  simpa only [map_subgroupOf_eq_of_le hinner, Subgroup.map_bot] using hm

theorem star_intersection_normalizer_control_of_inner
    (h : Input κ H R M K) [(K.subgroupOf H).Normal]
    (hinner : starImage K R R ≤ starImage K R K) :
    normalizer ((starImage K R R).subgroupOf (starImage K R K) :
        Set (starImage K R K)) ≤
      (starM K R M).subgroupOf (starImage K R K) := by
  let C := starImage K R K
  let U := (starImage K R R).subgroupOf C
  intro x hx
  have hn : (x : StarQuotient K R) ∈
      normalizer (starImage K R R : Set (StarQuotient K R)) := by
    rw [←map_subgroupOf_eq_of_le hinner]
    exact U.le_normalizer_map C.subtype ⟨x, hx, rfl⟩
  exact star_radical_normalizer_control h ⟨x.property, hn⟩

end CFSG.Quasithin.ChapterC.C27Source
