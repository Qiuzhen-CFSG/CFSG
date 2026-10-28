module
public import Theory.GroupTheory.PrimeIndexResidualContainment
public import Theory.GroupTheory.Fitting.TwoCorePreimage
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.PResidual.PrimeSection

/-!
# A normalized five-residual lies in the Fitting preimage

Suppose a two-perfect subgroup has two-core index five, and the preimage
of the quotient Fitting subgroup normalizes it. If it escaped the preimage,
prime index would put the intersection inside its two-core. Normality in the
Fitting preimage then puts their commutator inside the ambient two-core.
Self-centralization of F* in the quotient forces the desired containment.

Source application: Aschbacher--Smith, original15.2.4, printed p.1107.
-/

open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A prime-sized two-residual normalized by the Fitting preimage lies in it,
when the quotient generalized Fitting subgroup has no components. -/
public theorem residual_le_twoFittingCore_of_normalized (Y : Subgroup G) (hY : IsPPerfect 2 Y)
    (hc : (pCore 2 Y).index = 5)
    (hn : twoFittingCore G ≤ normalizer (Y : Set G))
    (hf : generalizedFitting (G ⧸ pCore 2 G) = fittingSubgroup (G ⧸ pCore 2 G)) :
    Y ≤ twoFittingCore G := by
  classical
  let F := twoFittingCore G
  let q := QuotientGroup.mk' (pCore 2 G)
  by_contra hout
  have hsup : Y ⊔ Y.pCoreIn 2 = Y := sup_eq_left.mpr (pCoreIn_le 2 Y)
  have hi : (Y.pCoreIn 2).relIndex (Y ⊔ Y.pCoreIn 2) = 5 := by
    rw [hsup]
    change ((pCore 2 Y).map Y.subtype).relIndex Y = 5
    rw [relIndex, subgroupOf, comap_map_eq_self_of_injective Y.subtype_injective]
    exact hc
  have hint : Y ⊓ F ≤ Y.pCoreIn 2 := by
    simpa only [hsup] using inf_le_pCore_of_prime_index_of_not_le hY
      (isPGroup_pCoreIn 2 Y) (by decide : Nat.Prime 5) hi
      (show Y ⊔ Y.pCoreIn 2 ≤ normalizer (F : Set G) from le_normalizer_of_normal) hout
  have hnormal : F ≤ normalizer ((Y ⊓ F : Subgroup G) : Set G) :=
    (le_inf hn F.le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hcore : Y ⊓ F ≤ pCore 2 G := by
    have hle := le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 Y).to_le hint)
      (show Y ⊓ F ≤ F from inf_le_right) hnormal
    exact hle.trans (pCoreIn_le_of_subnormal 2 (inferInstance : F.Normal).isSubnormal)
  have hcomm : ⁅Y,F⁆ ≤ pCore 2 G :=
    (le_inf (le_normalizer_iff_commutator_le_left.mp hn)
      (commutator_le_right Y F)).trans hcore
  have hFmap : F.map q = fittingSubgroup (G ⧸ pCore 2 G) :=
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have hcentral : Y.map q ≤ centralizer (fittingSubgroup (G ⧸ pCore 2 G) : Set _) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [←hFmap, ←map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hcomm
  apply hout
  change Y ≤ (fittingSubgroup (G ⧸ pCore 2 G)).comap q
  apply map_le_iff_le_comap.mp
  exact hcentral.trans (hf ▸ centralizer_generalizedFitting_le (G ⧸ pCore 2 G))

end Theory.GroupTheory
