module

public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.GuardedSource
public import CFSG.Quasithin.Chapter3.Section01.Source318Complete

/-!
# Fitting centralization with the source cubic bounds discharged

The simple QTKE hypothesis now proves the guarded cubic bound used both
for Xi-minus and for the original reduced quaternion-action module. The
actual escaping local subgroup supplies every outside-local witness.
The preceding 13.3.2 list remains its separate source premise; the
3.1.8 premise is discharged here for the literal star quotient and the
subsequent moved-component construction.

Source: Aschbacher--Smith, 13.3.14(d) and the following paragraph, p.892.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open SupercriticalSource
open Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Reduction 13.3.14(d), retaining only the independent preceding source list. -/
theorem source_centralizes_fitting_of_source1332
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (h1332 : Source1332OneTwo T)
    (H Lplus U M : Subgroup G)
    (hH : H ∈ Chapter1.He G) (hHlocal : IsTwoLocal H)
    (hTH : (T : Subgroup G) ≤ H) (hLH : Lplus ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (Lplus : Set G))
    (hL : IsPPerfect 2 Lplus) (hL3 : Nat.card (Lplus ⧸ pCore 2 Lplus) = 3)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M) (hescape : ¬ H ≤ M)
    (hU : U ≤ Stellmacher.omegaOneCenterAmbient (H.pCoreIn 2))
    (hY : ∀ p : ℕ, p.Prime → Odd p → primeRank p (centralizingResidual U) ≤ 1) :
    (star H Lplus hLH).pCoreIn 2 ≤
      centralizer (fittingSubgroup (Star H) : Set (Star H)) :=
  source_centralizes_fitting_of_guarded_sources hG T h1332
    (Chapter3.source_guardedTheorem318One hG) H Lplus U M
    hH hHlocal hTH hLH hTL hL hL3 hM hTM hescape hU hY

/-- The actual moved component after reduction (d), with both source cubic
bounds proved from the original simple QTKE hypothesis. -/
theorem source_moved_component_of_source1332
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (h1332 : Source1332OneTwo T)
    (H Lplus U M : Subgroup G)
    (hH : H ∈ Chapter1.He G) (hHlocal : IsTwoLocal H)
    (hTH : (T : Subgroup G) ≤ H) (hLH : Lplus ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (Lplus : Set G))
    (hL : IsPPerfect 2 Lplus) (hL3 : Nat.card (Lplus ⧸ pCore 2 Lplus) = 3)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M) (hescape : ¬ H ≤ M)
    (hU : U ≤ Stellmacher.omegaOneCenterAmbient (H.pCoreIn 2))
    (hY : ∀ p : ℕ, p.Prime → Odd p → primeRank p (centralizingResidual U) ≤ 1)
    (hne : pCore 2 (star H Lplus hLH) ≠ ⊥) :
    ∃ K : Subgroup H, K.IsCComponent ∧
      IsComponent (Star H) (K.map (QuotientGroup.mk' (pCore 2 H))) ∧
      ⁅K.map (QuotientGroup.mk' (pCore 2 H)), (star H Lplus hLH).pCoreIn 2⁆ ≠ ⊥ ∧
      Lplus.subgroupOf H ≤ normalizer (K : Set H) ∧
      ⁅K, Lplus.subgroupOf H⁆ = K ∧ IsQuasisimple (K ⧸ pCore 2 K) :=
  source_moved_component_of_guarded_sources hG T h1332
    (Chapter3.source_guardedTheorem318One hG) H Lplus U M
    hH hHlocal hTH hLH hTL hL hL3 hM hTM hescape hU hY hne

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
