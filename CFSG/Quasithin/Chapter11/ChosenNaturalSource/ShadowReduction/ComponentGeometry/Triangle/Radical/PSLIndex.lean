module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Radical.RelativeModels
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Radical.FittingImage
public import Theory.GroupTheory.AutomorphismOvergroupCore

/-!
# The Fitting index in the prime PSL₂ case

The radical of the perfect component is exactly its two-core. A normal
two-extension therefore also has radical equal to its two-core. Both
inclusions O₂ ≤ O₂,F ≤ O∞ then give index one. The actual normal subgroup
of KT and its Sylow supplement supply the extension, without splitting.
Source: Aschbacher--Smith 11.4.1(3), printed p.776.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical
variable {G : Type*} [Group G] [Finite G]

/-- The genuine PSL₂ quotient forces radical = two-core in KT. -/
theorem join_radical_eq_core_of_psl2 (T : Sylow 2 G) (K : Subgroup G)
    [Group.IsPerfect K] (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    {p : ℕ} (hp : 3 < p) (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 p) :
    solvableRadical (K ⊔ (T : Subgroup G) : Subgroup G) =
      pCore 2 (K ⊔ (T : Subgroup G) : Subgroup G) := by
  let J := K ⊔ (T : Subgroup G)
  let B := K.subgroupOf J
  let : B.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le K.le_normalizer hTK)
  let e : B ≃* K := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  have hRB : IsPGroup 2 (solvableRadical B) := by
    have hRK : IsPGroup 2 (solvableRadical K) :=
      (radical_eq_core_of_psl2 hp hm).symm ▸ pCore_isPGroup
    exact hRK.of_equiv ((e.subgroupMap (solvableRadical B)).trans
      (MulEquiv.subgroupCongr (map_solvableRadical_equiv e))).symm
  have hq : IsPGroup 2 (J ⧸ B) := isPGroup_quotient_of_sup_eq_top B
    ((T : Subgroup G).subgroupOf J) T.isPGroup'.comap_subtype (by
      rw [← subgroupOf_sup (show K ≤ J from le_sup_left)
        (show (T : Subgroup G) ≤ J from le_sup_right), subgroupOf_self])
  exact radical_eq_core_of_normal_two_quotient B hRB hq

/-- In this surviving branch the printed index-one-or-two step is index one. -/
theorem fitting_index_one_of_psl2 (T : Sylow 2 G) (K : Subgroup G)
    [Group.IsPerfect K] (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    {p : ℕ} (hp : 3 < p) (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 p) :
    (twoFittingCore (K ⊔ (T : Subgroup G) : Subgroup G)).relIndex
      (solvableRadical (K ⊔ (T : Subgroup G) : Subgroup G)) = 1 := by
  apply relIndex_eq_one.mpr
  rw [join_radical_eq_core_of_psl2 T K hTK hp hm]
  exact twoCore_le_twoFittingCore

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical
