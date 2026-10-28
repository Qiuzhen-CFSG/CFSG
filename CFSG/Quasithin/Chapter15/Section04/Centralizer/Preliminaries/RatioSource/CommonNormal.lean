module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.RatioSource.Setup

/-!
# The common-normal obstruction and nontriviality of the ratio module

The source 3.1.1 implication is stated with relative normality and the
two-residual O²(H). Applied to R=O₂(M₀), it contradicts the unique maximal
two-local overgroup. In particular, V=1 would force R=T by the original
kernel equality; T is Sylow in O²(H)T, so the same contradiction excludes
this degenerate case before applying D.1.5.

The universal earlier implication remains with qt-3-01 and qt-c-05. This
module proves its actual application, not that earlier source theorem.
Source: Aschbacher–Smith, Theorem 3.1.1, printed pp.571–572, and 15.4.2(4),
printed p.1156.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.RatioSource
open MaximalPrimeSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Genuine universal 3.1.1, with the full known-simple input and relative
normality; no ambient normality or common normal subgroup is assumed. -/
def Earlier311 : Prop :=
  ∀ T : Sylow 2 G, IsSimpleQTKE KnownSimple.IsKnownSimple G →
    ∀ A H R : Subgroup G,
    A ∈ Chapter1.HOver G (T : Set G) → H ∈ Chapter1.HOver G (T : Set G) →
    Order.HasUniqueMaximalOver (T : Subgroup G) H →
    R ≠ ⊥ → R ≤ T →
    Chapter1.IsSylowIn 2 R ((pResidual 2 H).map H.subtype ⊔ R) →
    A ≤ normalizer (R : Set G) →
    ∃ N : Subgroup G, N ≤ R ∧ N ≠ ⊥ ∧ Chapter3.NormalIn N (Chapter3.generated A H)

variable {T : Sylow 2 G} {M₀ M H : Subgroup G} {V : Subgroup M₀}

/-- The last contradiction in the source proof, with every 3.1.1 hypothesis checked. -/
theorem LocalHypotheses.not_core_sylow
    (l : LocalHypotheses T M₀ M V) (h : SourceHypotheses T)
    (h311 : Earlier311 (G := G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    ¬ Chapter1.IsSylowIn 2 (M₀.pCoreIn 2)
      ((pResidual 2 H).map H.subtype ⊔ M₀.pCoreIn 2) := by
  intro hs
  have hn : M₀ ≤ normalizer (M₀.pCoreIn 2 : Set G) := by
    simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map,
      range_subtype] using (pCore 2 M₀).le_normalizer_map M₀.subtype
  have hc := h311 T h.simpleQTKE M₀ H (M₀.pCoreIn 2) l.mem_H hH.1.1
    (Chapter3.HStar.hasUniqueMaximalOver T (l.mem_H.2.trans l.le_maximal) hH)
    l.mem_H.1 (l.core_eq_centralizer.le.trans inf_le_left) hs hn
  exact Chapter3.no_common_normal_of_unique_maximal (isPGroup_pCoreIn 2 M₀)
    l.unique hH.1.2 hc

/-- D.1.5's nontriviality condition follows from the actual source hypotheses. -/
theorem LocalHypotheses.module_ne_bot
    (l : LocalHypotheses T M₀ M V) (h : SourceHypotheses T)
    (h311 : Earlier311 (G := G)) : V.map M₀.subtype ≠ ⊥ := by
  intro hV
  obtain ⟨H, hH⟩ := exists_HStar h l.maximal
  have hcore : M₀.pCoreIn 2 = (T : Subgroup G) := by
    rw [l.core_eq_centralizer, hV]
    apply inf_eq_left.mpr
    intro x _ y hy
    rw [show y = 1 from mem_bot.mp hy, one_mul, mul_one]
  apply l.not_core_sylow h h311 hH
  rw [hcore]
  exact ⟨T.subtype le_sup_right, map_subgroupOf_eq_of_le le_sup_right⟩

omit [Finite G] in
/-- In the outside-core branch H is a genuine minimal parabolic. -/
theorem LocalHypotheses.minimalParabolic
    (l : LocalHypotheses T M₀ M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hout : ¬ V.map M₀.subtype ≤ H.pCoreIn 2) : ChapterB.IsMinimalParabolicOver T H := by
  apply Chapter3.HStar.minimalParabolic T (l.mem_H.2.trans l.le_maximal) hH
  right
  intro hn
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hnorm := (normal_subgroupOf_iff_le_normalizer hTH).mp hn
  have hTcore : (T : Subgroup G) ≤ H.pCoreIn 2 :=
    le_pCoreIn_of_normalizes T.isPGroup' hTH hnorm
  have hVT : V.map M₀.subtype ≤ (T : Subgroup G) :=
    (map_mono l.reduced.le_pCore).trans (l.core_eq_centralizer.le.trans inf_le_left)
  exact hout (hVT.trans hTcore)

/-- Characteristic two for the actual H used by D.1.4 and E.2.9. -/
theorem fitting_eq_core_of_HStar (h : SourceHypotheses T)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    generalizedFitting H = pCore 2 H := by
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  exact Chapter1.mem_He_iff.mp
    (Chapter1.lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T) hH.1.1)

end CFSG.Quasithin.Chapter15.Section04.RatioSource
