module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalThompson
public import CFSG.Quasithin.Chapter3.Section01.Source318Complete
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.SourceKnownSimple
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalThompson

/-!
# The cubic budget on the whole original rank-one module

The original reduced subgroup has centralizer O₂(LT). An actual outside
H-star member and nonsolvable maximal-local uniqueness therefore supply
source 3.1.8 on that entire subgroup. The bound is retained both on its
literal centralizer quotient and on the identical quotient (LT)/O₂(LT).
No constituent, model, Thompson movement, or numerical premise is supplied.

Source: Aschbacher–Smith 3.1.8 and the beginning of 5.1.3, pp.576,630–631.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}

private theorem cubic_quotient_congr
    {E : Type*} [Group E] (U C D : Subgroup E)
    [U.Normal] [IsElementaryAbelian 2 U] [C.Normal] [D.Normal]
    (hC : C = centralizer (U : Set E)) (hD : D = centralizer (U : Set E))
    (hb : cubicRatio (NormalElementaryQuotient.representation U
      (QuotientGroup.mk' C) (QuotientGroup.mk'_surjective C)
      ((QuotientGroup.ker_mk' C).trans hC)) ≤ 2) :
    cubicRatio (NormalElementaryQuotient.representation U
      (QuotientGroup.mk' D) (QuotientGroup.mk'_surjective D)
      ((QuotientGroup.ker_mk' D).trans hD)) ≤ 2 := by
  subst C
  subst D
  exact hb

/-- The original reduced module has precisely the local two-core as kernel. -/
theorem Input.reduced_centralizer_eq_twoCore
    (h : Input KnownSimple.IsKnownSimple T L W n) :
    centralizer (W.subgroupOf (L ⊔ (T : Subgroup G)) :
      Set (L ⊔ (T : Subgroup G) : Subgroup G)) =
        pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) :=
  h.reduced_centralizer_core

/-- The full original reduced action has cubic ratio at most two, on its
actual centralizer quotient. -/
theorem Input.reduced_quotient_cubicRatio_le_two
    (h : Input KnownSimple.IsKnownSimple T L W n) :
    let J := L ⊔ (T : Subgroup G)
    let U := W.subgroupOf J
    letI := h.reduced_internal.normal
    letI := h.reduced_internal.elementary
    cubicRatio (NormalElementaryQuotient.representation U
      (QuotientGroup.mk' (centralizer (U : Set J)))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ≤ 2 := by
  let J := L ⊔ (T : Subgroup G)
  let U := W.subgroupOf J
  let := h.reduced_internal.normal
  let := h.reduced_internal.elementary
  obtain ⟨H, hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside h.outside
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple h.qtke T h.maximal_local
  have horbit : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L T L le_rfl h.sylow_normalizes)
      (le_componentOrbit L T)
  have huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N → J ≤ N →
      N = normalizer (L : Set G) := by
    simpa only [horbit] using hu.normalizer_unique
  have hQ : pCore 2 J ≤ (T : Subgroup G).subgroupOf J := by
    exact pCore_isPGroup.le_sylow_of_normal
      (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right))
  have hc : (T : Subgroup G).subgroupOf J ⊓ centralizer (U : Set J) = pCore 2 J := by
    rw [h.reduced_centralizer_core, inf_eq_right.mpr hQ]
  exact Chapter3.source_reduced_join_cubicRatio_le_two h.qtke T
    (normalizer (L : Set G)) L H h.original_section1221.maximal_faithful.2.1.2.1
    L.le_normalizer (normal_subgroupOf_of_le_normalizer le_rfl) h.maximal
    (sup_le L.le_normalizer h.sylow_normalizes) huniq hH U h.reduced_internal hc

/-- The same full-module cubic budget on the canonical quotient (LT)/O₂(LT),
with its exact original conjugation action. -/
theorem Input.core_quotient_cubicRatio_le_two
    (h : Input KnownSimple.IsKnownSimple T L W n) :
    let J := L ⊔ (T : Subgroup G)
    let U := W.subgroupOf J
    letI := h.reduced_internal.normal
    letI := h.reduced_internal.elementary
    let q := QuotientGroup.mk' (pCore 2 J)
    let hk : q.ker = centralizer (U : Set J) :=
      (QuotientGroup.ker_mk' _).trans h.reduced_centralizer_eq_twoCore.symm
    cubicRatio (NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective _) hk) ≤ 2 := by
  let := h.reduced_internal.normal
  let := h.reduced_internal.elementary
  exact cubic_quotient_congr _ _ _ rfl h.reduced_centralizer_eq_twoCore.symm
    h.reduced_quotient_cubicRatio_le_two

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
