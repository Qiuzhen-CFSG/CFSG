module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Point
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.DoubleNaturalExcludedSetup
public import Theory.GroupTheory.CharacteristicNormalizerRestriction

/-!
# Characteristic-normalizer control at a nonsingular point

The original Q=O₂(LT)=C_T(W) centralizes every point of W. Uniqueness for
LT bounds C(G,Q) by N_G(L). Restricting characteristic normalizers through
the literal embedding G_w → G gives C(G_w,Q) ≤ M_w, the control premise
used in C.2.3 at the start of 12.1.1. Radicality and the Sylow normal-closure
condition are separate source conclusions, not consequences asserted here.

Source: Aschbacher--Smith 1.4.1(1), 12.1.1, printed pp.514,788.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Original 1.4.1(1) for the exact two-core appearing in 12.1.1. -/
theorem doubleNatural_core_characteristicNormalizerClosure
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V) :
    ((L ⊔ (T : Subgroup G)).pCoreIn 2).characteristicNormalizerClosure ≤
      normalizer (L : Set G) := by
  exact characteristicNormalizerClosure_le_of_unique_twoLocal (isPGroup_pCoreIn 2 _)
    ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
    (D.doubledNormalizer_unique h).2

/-- The original Q lies in every G_w, using C_T(W)=Q rather than an assumed
point-core equality. -/
theorem doubleNatural_core_le_pointCentralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) (w : componentOrbit V (T : Subgroup G)) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ B.pointCentralizer w := by
  rw [← D.doubledOrbit_sylow_centralizer h]
  intro q hq
  exact mem_centralizer_singleton_iff.mpr (hq.2 (w : G) w.property).symm

/-- The characteristic-normalizer control premise inside the actual G_w. -/
theorem doubleNatural_point_characteristicNormalizerClosure
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) (w : componentOrbit V (T : Subgroup G)) :
    (((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf
      (B.pointCentralizer w)).characteristicNormalizerClosure ≤
        (B.localPointCentralizer w).subgroupOf (B.pointCentralizer w) := by
  intro x hx
  have hh := map_characteristicNormalizerClosure_le (B.pointCentralizer w).subtype
    (B.pointCentralizer w).subtype_injective
    (((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf (B.pointCentralizer w))
  rw [map_subgroupOf_eq_of_le (D.doubleNatural_core_le_pointCentralizer h B w)] at hh
  exact ⟨D.doubleNatural_core_characteristicNormalizerClosure h
    (hh (mem_map_of_mem _ hx)), x.property⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
