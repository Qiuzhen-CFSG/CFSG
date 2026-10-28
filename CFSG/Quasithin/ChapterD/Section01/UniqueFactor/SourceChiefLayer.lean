module
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.NormalClosure
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.ChiefLayer
public import Theory.GroupTheory.NoncentralChiefRefinement.UniqueResidualLayer
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.ConjugateSpanKernel
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Constructing the original unique-chief-layer geometry

In the actual qrc configuration, U=[U,O²(G₂)]V because the Sylow
subgroup normalizes V and supplements O²(G₂). The commutator is
idempotent and nontrivial: otherwise G₂ would normalize V, contrary
to the common-normal hypothesis. The genuine one-factor chief series
supplies the normal-subgroup dichotomy and constructs ChiefLayerGeometry.

The same argument excludes a zero noncentral-factor count for every
actual chief series on U when V is nontrivial. All finiteness is local
to G₂; the original ambient group need not be finite.
Source: Aschbacher–Smith, D.1.4–5, pp.175–177.
-/

public section
namespace CFSG.Quasithin.ChapterD.UniqueFactor
open Subgroup
variable {G : Type*} [Group G] {G₁ G₂ T V : Subgroup G}

private theorem residual_sup_sylow (d : QRCConfiguration G₁ G₂ T V) :
    (pResidual 2 G₂).map G₂.subtype ⊔ T = G₂ := by
  let := d.finite_right
  obtain ⟨S, hS⟩ := d.sylow_right
  have h := congrArg (map G₂.subtype) (pResidual_sup_sylow_eq_top S)
  rw [Subgroup.map_sup, hS, ← MonoidHom.range_eq_map, range_subtype] at h
  exact h

private theorem span_le_right (d : QRCConfiguration G₁ G₂ T V)
    (hV : V ≤ twoCoreIn G₂) : conjugateSpan G₂ V ≤ G₂ :=
  (span_le_right_core d hV).trans (twoCore_le G₂)

private theorem moved_normalized (d : QRCConfiguration G₁ G₂ T V)
    (hV : V ≤ twoCoreIn G₂) :
    G₂ ≤ normalizer ((⁅conjugateSpan G₂ V, (pResidual 2 G₂).map G₂.subtype⁆ : Subgroup G) : Set G) := by
  let U := conjugateSpan G₂ V
  have he : ((⁅U.subgroupOf G₂, pResidual 2 G₂⁆ : Subgroup G₂)).map G₂.subtype =
      ⁅U, (pResidual 2 G₂).map G₂.subtype⁆ := by
    rw [map_commutator, map_subgroupOf_eq_of_le (span_le_right d hV)]
  have hn := (⁅U.subgroupOf G₂, pResidual 2 G₂⁆ : Subgroup G₂).le_normalizer_map G₂.subtype
  rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype, he] at hn
  exact hn

theorem residual_commutator_idempotent (d : QRCConfiguration G₁ G₂ T V)
    (hV : V ≤ twoCoreIn G₂) :
    ⁅⁅conjugateSpan G₂ V, (pResidual 2 G₂).map G₂.subtype⁆,
      (pResidual 2 G₂).map G₂.subtype⁆ =
      ⁅conjugateSpan G₂ V, (pResidual 2 G₂).map G₂.subtype⁆ := by
  let := d.finite_right
  let U := conjugateSpan G₂ V
  have hp : IsPGroup 2 (U.subgroupOf G₂) :=
    ((isPGroup_pCoreIn 2 G₂).to_le (span_le_right_core d hV)).comap_subtype
  have h := commutator_isPPerfect_idempotent (pResidual 2 G₂) (U.subgroupOf G₂)
    (isPPerfect_pResidual 2) hp le_normalizer_of_normal
  have hm := congrArg (map G₂.subtype) h
  simpa only [U, map_commutator, map_subgroupOf_eq_of_le (span_le_right d hV)] using hm

theorem span_eq_residual_commutator_sup (d : QRCConfiguration G₁ G₂ T V)
    (hV : V ≤ twoCoreIn G₂) :
    conjugateSpan G₂ V =
      ⁅conjugateSpan G₂ V, (pResidual 2 G₂).map G₂.subtype⁆ ⊔ V := by
  have he := residual_sup_sylow d
  have hn : T ≤ normalizer
      ((⁅conjugateSpanBy V ((pResidual 2 G₂).map G₂.subtype ⊔ T),
        (pResidual 2 G₂).map G₂.subtype⁆ : Subgroup G) : Set G) := by
    rw [he, ← conjugateSpan_eq]
    exact (sylow_le_right d).trans (moved_normalized d hV)
  have hc := conjugateSpanBy_sup_eq_span_sup_commutator V
    ((pResidual 2 G₂).map G₂.subtype) T hn
  rw [he, ← conjugateSpan_eq, ← conjugateSpan_eq,
    conjugateSpan_eq_of_normalized T V ((sylow_le_left d).trans d.module_normalized),
    sup_comm] at hc
  exact hc

theorem residual_commutator_ne_bot (d : QRCConfiguration G₁ G₂ T V)
    (hne : V ≠ ⊥) :
    ⁅conjugateSpan G₂ V, (pResidual 2 G₂).map G₂.subtype⁆ ≠ ⊥ := by
  intro hz
  have hKV : (pResidual 2 G₂).map G₂.subtype ≤ centralizer (V : Set G) :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz)).trans
      (centralizer_le (le_conjugateSpan G₂ V))
  apply d.module_not_normalized_right hne
  rw [← residual_sup_sylow d]
  exact sup_le (hKV.trans (centralizer_le_normalizer (V : Set G)))
    ((sylow_le_left d).trans d.module_normalized)

theorem source_chiefLayerGeometry (d : QRCConfiguration G₁ G₂ T V)
    (hV : V ≤ twoCoreIn G₂) (hu : HasUniqueNoncentralChiefFactor G₂ V) :
    ChiefLayerGeometry G₂ V := by
  let := d.finite_right
  let U := conjugateSpan G₂ V
  have hUG : U ≤ G₂ := span_le_right d hV
  have hp : IsPGroup 2 (U.subgroupOf G₂) :=
    ((isPGroup_pCoreIn 2 G₂).to_le (span_le_right_core d hV)).comap_subtype
  refine ⟨residual_commutator_ne_bot d (module_ne_bot hu),
    residual_commutator_idempotent d hV, span_eq_residual_commutator_sup d hV, ?_⟩
  intro X hXU hXn
  let : (X.subgroupOf G₂).Normal := normal_subgroupOf_of_le_normalizer hXn
  obtain ⟨s, hs⟩ := hu
  rcases s.residual_dichotomy_of_count_one hp hs (X.subgroupOf G₂)
    (subgroupOf_mono G₂ hXU) with hzero | hle
  · left
    have hh := congrArg (map G₂.subtype) hzero
    simpa only [map_commutator, map_subgroupOf_eq_of_le (hXU.trans hUG), Subgroup.map_bot] using hh
  · right
    have hh := map_mono (f := G₂.subtype) hle
    simpa only [U, map_commutator, map_subgroupOf_eq_of_le (span_le_right d hV),
      map_subgroupOf_eq_of_le (hXU.trans hUG)] using hh
theorem noncentralCount_ne_zero (d : QRCConfiguration G₁ G₂ T V)
    (hne : V ≠ ⊥) (hV : V ≤ twoCoreIn G₂)
    (s : NoncentralChiefRefinement.SeriesOn ((conjugateSpan G₂ V).subgroupOf G₂)) :
    s.noncentralCount ≠ 0 := by
  let := d.finite_right
  have hp : IsPGroup 2 ((conjugateSpan G₂ V).subgroupOf G₂) :=
    ((isPGroup_pCoreIn 2 G₂).to_le (span_le_right_core d hV)).comap_subtype
  intro hz
  have hpLast : IsPGroup 2 s.series.last.val := hp.of_equiv
    (MulEquiv.subgroupCongr (congrArg Subtype.val s.last_eq)).symm
  have hc := s.series.residual_commutator_le_head_of_count_zero hpLast
    ((s.noncentralCount_eq_twoCount hp).symm.trans hz)
  rw [s.head_eq, s.last_eq] at hc
  change ⁅(conjugateSpan G₂ V).subgroupOf G₂, pResidual 2 G₂⁆ ≤ ⊥ at hc
  have hm := map_mono (f := G₂.subtype) hc
  rw [map_commutator, map_subgroupOf_eq_of_le (span_le_right d hV), Subgroup.map_bot] at hm
  exact residual_commutator_ne_bot d hne (le_bot_iff.mp hm)

end CFSG.Quasithin.ChapterD.UniqueFactor
