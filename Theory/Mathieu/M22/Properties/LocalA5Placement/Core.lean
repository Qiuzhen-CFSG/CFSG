module

public import Theory.Mathieu.M22.ChapterHLocalClassification
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.PCoreInRestriction

/-!
# Two intrinsic core possibilities for a local M22 component

Subnormality in the join with a full Sylow places the subgroup's intrinsic
two-core in that same Sylow. The native order-sixteen elementary catalogue
then leaves precisely the hexad and quintet kernels. No normality of the
original subgroup is required.

Source: Aschbacher--Smith A.3.12(12) and A.3.14(6), pp.47--49, using the
simultaneous Sylow arrangement and two-E16 catalogue of H.14.3(1), p.397.
-/

public section
open Subgroup Theory.GroupTheory Sporadic.Mathieu MathieuCode
namespace Sporadic.Mathieu.M22LocalA5Placement

theorem core_le_sylow {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (B : Subgroup G)
    (hB : (B.subgroupOf (B ⊔ (S : Subgroup G))).IsSubnormal) :
    B.pCoreIn 2 ≤ (S : Subgroup G) := by
  let H := B ⊔ (S : Subgroup G)
  have hle := map_mono (f := H.subtype) (pCoreIn_le_of_subnormal 2 hB)
  rw [pCoreIn_subgroupOf 2 B H le_sup_left,
    map_subgroupOf_eq_of_le ((B.pCoreIn_le 2).trans le_sup_left)] at hle
  change B.pCoreIn 2 ≤ H.pCoreIn 2 at hle
  have hs := pCoreIn_le_sylow H (S.subtype le_sup_right)
  rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] at hs
  exact hle.trans hs

theorem marked_core_cases (B : Subgroup M22)
    (hB : (B.subgroupOf (B ⊔ M22ChapterH.CompatibleSylow.inner.toSubgroup)).IsSubnormal)
    (he : IsElementaryAbelian 2 (B.pCoreIn 2))
    (hc : Nat.card (B.pCoreIn 2) = 16) :
    B.pCoreIn 2 = m22InnerHexadKernel m22SourceOctad ∨
      B.pCoreIn 2 = m22InnerQuintetKernel m22SourceSextet :=
  (M22ChapterH.intrinsic_sylow_catalogue.2.1 (B.pCoreIn 2)).mp
    ⟨he, hc, core_le_sylow M22ChapterH.CompatibleSylow.inner B hB⟩

end Sporadic.Mathieu.M22LocalA5Placement
