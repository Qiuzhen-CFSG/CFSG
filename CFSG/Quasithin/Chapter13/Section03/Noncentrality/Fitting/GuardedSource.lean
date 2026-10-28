module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.SupercriticalSource.StarPlacement
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.SupercriticalSource.XiSource
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.QuaternionReducedSource
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting
public import CFSG.Quasithin.Chapter3.Section02.SourceXiMinusGuarded
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.OrbitSource

/-!
# Fitting centralization from the guarded earlier source theorems

The original local subgroup escapes the maximal local M. Extending it to
another maximal two-local supplies the standing outside witness at every
selected Xi normalizer. A moving odd core then gives the genuine selected
supercritical subgroup, its SL₂(3) action and its marked quaternion image.
The preceding 13.3.2 list and guarded 3.1.8 imply Xi-minus, hence the literal
E₉ quotient. Its action on R₂(PT) has cubic ratio greater than two; applying
that same guarded source theorem to R₂(PT) gives the contradiction. The
Sylow centralizer is proved by comparison with the original Xi module.

The final theorem constructs the moved component immediately after (d),
discharging its orbit bound from the actual SQTK local group. The earlier
13.3.2 list and guarded 3.1.8 remain explicit source obligations; this file
does not assert that maximal-counterexample data alone produce them.
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

private theorem outside_each_maximal
    (T : Sylow 2 G) (M H : Subgroup G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hH : IsTwoLocal H) (hTH : (T : Subgroup G) ≤ H) (hescape : ¬ H ≤ M)
    (N : Subgroup G) (hN : IsMaximalTwoLocal N) (hTN : (T : Subgroup G) ≤ N) :
    Chapter3.HasMaximalOutside T N := by
  by_cases he : N = M
  · subst N
    obtain ⟨K,hHK,hK⟩ := Finite.exists_le_maximal hH
    exact Chapter3.hasMaximalOutside_of_two_distinct hM hK hTM (hTH.trans hHK)
      (by intro he; exact hescape (he ▸ hHK))
  · exact Chapter3.hasMaximalOutside_of_two_distinct hN hM hTN hTM (Ne.symm he)

private theorem reduced_ratio_le_of_guarded
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h318 : Chapter3.GuardedSourceTheorem318One G) (T : Sylow 2 G)
    {X : Subgroup G} (hX : X ∈ Chapter1.XiStarF G (T : Subgroup G))
    (hout : Chapter3.HasMaximalOutside T (normalizer (X : Set G))) :
    let W := reducedTwoSubgroup (X ⊔ (T : Subgroup G) : Subgroup G)
    letI := (isPReduced_reducedPSubgroup (p := 2)
      (G := (X ⊔ (T : Subgroup G) : Subgroup G))).elementary
    let C := centralizer (W : Set (X ⊔ (T : Subgroup G) : Subgroup G))
    Representation.BinaryOffender.cubicRatio
      (Representation.NormalElementaryQuotient.representation W (QuotientGroup.mk' C)
        (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)) ≤ 2 := by
  obtain ⟨hmax,hu⟩ := Chapter1.XiEmbedding.normalizer_unique_of_XiStar_knownSimple hG T hX.2
  have hunique (N : Subgroup G) (hN : IsMaximalTwoLocal N)
      (hle : X ⊔ (T : Subgroup G) ≤ N) : N = normalizer (X : Set G) := by
    have hm : N ∈ {M : Subgroup G | IsMaximalTwoLocal M ∧ X ⊔ (T : Subgroup G) ≤ M} := ⟨hN,hle⟩
    rw [hu] at hm
    exact Set.mem_singleton_iff.mp hm
  have hAt := Chapter3.sourceTheorem318OneAt_of_guarded h318 hmax hX.1.1.invariant hout
  have hc := source_sylow_centralizer_eq_core T hX.1.1
    (sourceModule_ne_bot_of_mem_XiF hX.1)
  rw [sourceModule_centralizer_eq_reduced T hX.1.1] at hc
  exact hAt.cubicRatio_le X hX.1.1.perfect X.le_normalizer inferInstance hmax
    (sup_le X.le_normalizer hX.1.1.invariant) hunique
    (reducedTwoSubgroup (X ⊔ (T : Subgroup G) : Subgroup G))
    (isPReduced_reducedPSubgroup (p := 2) (G := (X ⊔ (T : Subgroup G) : Subgroup G))) hc

/-- The selected two-core centralizes the Fitting subgroup of the literal star quotient. -/
theorem source_centralizes_fitting_of_guarded_sources
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (h1332 : Source1332OneTwo T) (h318 : Chapter3.GuardedSourceTheorem318One G)
    (H Lplus U M : Subgroup G)
    (hH : H ∈ Chapter1.He G) (hHlocal : IsTwoLocal H)
    (hTH : (T : Subgroup G) ≤ H) (hLH : Lplus ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (Lplus : Set G))
    (hL : IsPPerfect 2 Lplus) (hL3 : Nat.card (Lplus ⧸ pCore 2 Lplus) = 3)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M) (hescape : ¬ H ≤ M)
    (hU : U ≤ Stellmacher.omegaOneCenterAmbient (H.pCoreIn 2))
    (hY : ∀ p : ℕ, p.Prime → Odd p → primeRank p (centralizingResidual U) ≤ 1) :
    (star H Lplus hLH).pCoreIn 2 ≤
      centralizer (fittingSubgroup (Star H) : Set (Star H)) := by
  have hout := outside_each_maximal T M H hM hTM hHlocal hTH hescape
  have hr (p : ℕ) (hp : p.Prime) (ho : Odd p) : primeRank p (Star H) ≤ 2 := by
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 H) pCore_isPGroup).trans
      ((hG.twoLocal_sqtk hHlocal).stronglyQuasithin p hp ho)
  apply centralizes_fitting_of_odd_cores
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  by_contra hm
  obtain ⟨D,hD,hle,hrD,hmodel,hmove,_,hQ,_,hXi,_⟩ :=
    source_selected_XiF_cubic T H Lplus U hH hTH hLH hTL hL hL3 ho
      (hr p hp ho) hm hU (hY p hp ho)
  let : D.Characteristic := hD
  have hstar := source_XiF_subset_XiStarF hG T h1332 hXi
  have hminus := Chapter3.SourceXiMinus.source_XiStarF_subset_XiMinus_of_guarded318
    hG h318 T hout hstar
  obtain ⟨_,hEA,hcard,_⟩ := star_residual_nine_of_XiMinus T H Lplus hLH hL hL3
    D ho hmodel hrD.le (hr 3 (by decide) (by decide)) hminus hmove
  let : IsElementaryAbelian 3 D := hEA
  have hgt := star_reduced_join_quaternion_ratio H T Lplus hTH hLH T.isPGroup'
    D hcard hXi.2 hQ
  have hle := reduced_ratio_le_of_guarded hG h318 T hstar
    (hout _ (Chapter1.XiEmbedding.normalizer_unique_of_XiStar_knownSimple hG T hstar.2).1
      hstar.1.1.invariant)
  exact not_lt_of_ge hle hgt

/-- Apply reduction (d) to the actual component construction after 13.3.14(d).
Only reduction (c)'s nontrivial star core remains as a separate local premise. -/
theorem source_moved_component_of_guarded_sources
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (h1332 : Source1332OneTwo T) (h318 : Chapter3.GuardedSourceTheorem318One G)
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
      ⁅K, Lplus.subgroupOf H⁆ = K ∧ IsQuasisimple (K ⧸ pCore 2 K) := by
  apply exists_moved_component_of_fitting_centralization H Lplus hLH hL
    (fun _ hK => Chapter1.Section02.component_normal_or_index_two_source
      (hG.twoLocal_sqtk hHlocal) hK) hne
  exact source_centralizes_fitting_of_guarded_sources hG T h1332 h318 H Lplus U M
    hH hHlocal hTH hLH hTL hL hL3 hM hTM hescape hU hY

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
