module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceIrreducible
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.DoubleNaturalExcludedSetup
public import CFSG.Quasithin.ChapterE.Section06.Basic
public import CFSG.Quasithin.ChapterE.GenerationKnownSimple
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
public import Theory.ElementaryAbelian.PrimeRankCard

/-!
# The actual normalized orbit in the Mathieu weak-closure argument

In the invariant-seed branch, non-FF kills the seed's fixed layer. The
original chosen-module TI theorem and the literal two-core identity then
construct every clause of E.6.1 inside M = N_G(L). In particular, M need
not equal N_G(W). Its local centralizers normalize W, and their fixed spaces
contain the original subspaces under consideration.

The original singleton uniqueness statement for N_G(C_T(W)) also gives
min(w,r) ≤ n(H) for every actual outside H*. The full known-simple
E-generation theorem supplies attainment; no positive-parameter hypothesis
is added. The completed Mathieu generation bound gives min(w,r) ≤ 2, and the
order-eleven displacement gives rank at least ten. The nonzero escaping-space
estimate remains with this task for the final global bounds and J₄ assembly.

Source: Aschbacher--Smith, 7.0.2--7.3.4, printed pp.695--699;
E.3.35 and E.6.1--2, pp.238 and244--245; the application in12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterE.Section06
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The literal E.6.1 configuration, including relative normality, the TI
condition under N_G(L), and the original uniqueness subgroup. -/
theorem sourceOrbit_hypothesisE61_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hVW : V = D.sourceOrbit) :
    HypothesisE61 KnownSimple.IsKnownSimple T (normalizer (L : Set G)) D.sourceOrbit := by
  have hjoin : L ⊔ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    sup_le L.le_normalizer D.sylow_normalizes_component
  have hnorm : L ⊔ (T : Subgroup G) ≤ normalizer (D.sourceOrbit : Set G) :=
    sup_le D.sourceOrbit_component_normalizes D.sourceOrbit_weakClosure_setup.normalizes
  have hcore : sylowCentralizer (T : Subgroup G) D.sourceOrbit =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    change (T : Subgroup G) ⊓ centralizer (D.sourceOrbit : Set G) = _
    rw [D.sourceOrbit_eq]
    exact D.orbit_centralizer h.toHypothesis1221
  refine ⟨h.simpleQTKE, (D.doubledNormalizer_unique h).1,
    D.sylow_normalizes_component, D.sourceOrbit_weakClosure_setup.nontrivial,
    inferInstance, D.sourceOrbit_weakClosure_setup.le_sylow,
    normal_subgroupOf_of_le_normalizer D.sourceOrbit_weakClosure_setup.normalizes, ?_, ?_⟩
  · intro g hg
    rw [← hVW]
    exact D.ti_of_centralizer_eq_bot h.toHypothesis1221
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
      (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
      (D.sourceOrbit_fixed_and_thompson_of_many h hmany hnon).1 g hg
  · intro N hN hle
    apply (D.doubledNormalizer_unique h).2 N hN
    apply le_trans _ hle
    refine le_inf (le_inf hjoin hnorm) ?_
    rw [hcore]
    exact (L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

/-- A nonzero source subspace lies in the fixed space of its actual local
centralizer image. TI supplies normalization; the action is Aut_G(W). -/
theorem sourceOrbit_localCentralizer_fixedSpace
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hVW : V = D.sourceOrbit) {U : Subgroup G} (hU : U ≠ ⊥) (hUV : U ≤ D.sourceOrbit) :
    U ≤ Chapter7.ambientSubmodule D.sourceOrbit
      (fixedSpace (automizerRepresentation D.sourceOrbit)
        (inducedAutomizer D.sourceOrbit (normalizer (L : Set G) ⊓ centralizer (U : Set G)))) := by
  have hE := D.sourceOrbit_hypothesisE61_of_many h hmany hnon hVW
  rw [Chapter7.ambientSubmodule_fixedSpace _ _ (hE.localCentralizer_le_normalizer hU hUV)]
  exact le_inf hUV (le_centralizer_iff.mpr inf_le_right)

/-- E.3.35 on W itself, rather than its possibly larger N_G(L)-orbit.
The source H* membership supplies SQTK and the original Sylow placement. -/
theorem sourceOrbit_min_parameters_le_generation
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    min (globalW D.sourceOrbit (T : Subgroup G)) (globalR D.sourceOrbit) ≤
      (generationParameter H : ℕ∞) := by
  apply le_of_not_gt
  intro hn
  apply hH.1.2
  apply ChapterE.SourceContainment.le_of_sqtk_knownSimple
    D.sourceOrbit_weakClosure_setup (T.subtype hH.1.1.2)
    (Chapter3.sqtk_of_mem_H h.simpleQTKE hH.1.1.1)
  · rw [D.sourceOrbit_eq]
    exact D.doubledOrbit_centralizer_unique h
  · exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
      (D.sourceOrbit_normalizer_le h.toHypothesis1221))
  · change (T : Subgroup G) ⊓ centralizer (D.sourceOrbit : Set G) ≤
      ((T : Subgroup G).subgroupOf H).map H.subtype
    rw [map_subgroupOf_eq_of_le hH.1.1.2]
    exact inf_le_left
  · exact hn

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterE.Section06
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Translate an escaping-subspace rank estimate relative to M = N_G(L)
to the full globalR minimum relative to N_G(W). The zero subspace is handled
by the dimension bound, separately from the nonzero TI argument. -/
theorem sourceOrbit_globalR_lower_of_local_ranks
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hVW : V = D.sourceOrbit) {k : ℕ} (hk : k ≤ rank D.sourceOrbit)
    (hlocal : ∀ U : Subgroup G, U ≤ D.sourceOrbit → U ≠ ⊥ →
      ¬ centralizer (U : Set G) ≤ normalizer (L : Set G) →
        k + rank U ≤ rank D.sourceOrbit) :
    (k : ℕ∞) ≤ globalR D.sourceOrbit := by
  have hE := D.sourceOrbit_hypothesisE61_of_many h hmany hnon hVW
  apply le_iInf
  intro U
  apply le_iInf
  rintro ⟨hUV, hescape⟩
  have hadd := offender_corank_add (B := (⊥ : Subgroup G)) bot_le hUV
  have hdim : rank D.sourceOrbit = subgroupCorank D.sourceOrbit U + rank U := by
    simpa only [subgroupCorank, relIndex_bot_left, rank] using hadd
  have hbound : k + rank U ≤ rank D.sourceOrbit := by
    by_cases hU : U = ⊥
    · simpa [hU, rank] using hk
    · exact hlocal U hUV hU (fun hM => hescape ((hE.centralizer_le_iff hU hUV).mp hM))
  exact_mod_cast (show k ≤ subgroupCorank D.sourceOrbit U by omega)

/-- Once r > 2, the actual outside-overgroup generation bound gives w ≤ 2.
The multiple-overgroup hypothesis constructs the H* witness. -/
theorem sourceOrbit_globalW_le_two_of_generation
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hr : (2 : ℕ∞) < globalR D.sourceOrbit)
    (hgen : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      generationParameter H ≤ 2) :
    globalW D.sourceOrbit (T : Subgroup G) ≤ 2 := by
  obtain ⟨H, hH⟩ := D.doubledOrbit_outside_of_many h hmany
  have hb : (generationParameter H : ℕ∞) ≤ 2 := by exact_mod_cast hgen H hH
  have hw := (min_le_iff.mp (D.sourceOrbit_min_parameters_le_generation h hH)).resolve_right
    (not_le_of_gt (lt_of_le_of_lt hb hr))
  exact hw.trans hb

/-- Conditional assembly of the two source bounds on the original orbit.
The Mathieu row calculations must still provide hdim, hlocal, and hgen. -/
theorem sourceOrbit_mathieu_bounds_of_local_estimates
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hVW : V = D.sourceOrbit) (hdim : 6 ≤ rank D.sourceOrbit)
    (hlocal : ∀ U : Subgroup G, U ≤ D.sourceOrbit → U ≠ ⊥ →
      ¬ centralizer (U : Set G) ≤ normalizer (L : Set G) →
        6 + rank U ≤ rank D.sourceOrbit)
    (hgen : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      generationParameter H ≤ 2) :
    globalW D.sourceOrbit (T : Subgroup G) ≤ 2 ∧ 6 ≤ globalR D.sourceOrbit := by
  have hr := D.sourceOrbit_globalR_lower_of_local_ranks h hmany hnon hVW hdim hlocal
  exact ⟨D.sourceOrbit_globalW_le_two_of_generation h hmany
    (lt_of_lt_of_le (by decide : (2 : ℕ∞) < 6) hr) hgen, hr⟩

/-- The actual7.5.4 consumer, now with the global minima discharged from
local rank and generation estimates. Those estimates remain source obligations. -/
theorem sourceOrbit_not_m23Code_of_local_estimates
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hVW : V = D.sourceOrbit) (hdim : 6 ≤ rank D.sourceOrbit)
    (hlocal : ∀ U : Subgroup G, U ≤ D.sourceOrbit → U ≠ ⊥ →
      ¬ centralizer (U : Set G) ≤ normalizer (L : Set G) →
        6 + rank U ≤ rank D.sourceOrbit)
    (hgen : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      generationParameter H ≤ 2) :
    ¬ MathieuCode.IsM23Code (automizerRepresentation D.sourceOrbit) := by
  obtain ⟨hw, hr⟩ := D.sourceOrbit_mathieu_bounds_of_local_estimates
    h hmany hnon hVW hdim hlocal hgen
  exact D.sourceOrbit_not_m23Code_of_many h hmany hnon hw hr

/-- The actual Mathieu quotient moves at least ten binary dimensions. This
handles the zero subspace in the global minimum without a rank hypothesis. -/
theorem sourceOrbit_mathieu_rank_ge_ten
    (hVW : V = D.sourceOrbit)
    (hm : Chapter7.NormalizedSource.HasMathieuCentralQuotient D.orbitComponent) :
    10 ≤ rank D.sourceOrbit := by
  have hr := D.sourceOrbit_mathieu_twoRank_ge_ten hVW hm
  rw [hVW] at hr
  simpa only [rank, IsElementaryAbelian.log_card_eq_primeRank] using hr

/-- The outside-overgroup comparison and the completed Mathieu Hall--Cartan
bound give min(w,r) ≤ 2 on the literal orbit, without any local rank premise. -/
theorem sourceOrbit_mathieu_min_parameters_le_two
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hVW : V = D.sourceOrbit)
    (hm : Chapter7.NormalizedSource.HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    min (globalW D.sourceOrbit (T : Subgroup G)) (globalR D.sourceOrbit) ≤ 2 := by
  obtain ⟨H, hH⟩ := D.doubledOrbit_outside_of_many h hmany
  apply (D.sourceOrbit_min_parameters_le_generation h hH).trans
  exact_mod_cast D.sourceOrbit_mathieu_generation_le_two_of_many h hmany hVW hm hnon hH

/-- The Mathieu generation theorem supplies w ≤ 2 as soon as r > 2. -/
theorem sourceOrbit_mathieu_globalW_le_two_of_globalR
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hVW : V = D.sourceOrbit)
    (hm : Chapter7.NormalizedSource.HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hr : (2 : ℕ∞) < globalR D.sourceOrbit) :
    globalW D.sourceOrbit (T : Subgroup G) ≤ 2 :=
  (min_le_iff.mp (D.sourceOrbit_mathieu_min_parameters_le_two h hmany hVW hm hnon)).resolve_right
    (not_le_of_gt hr)

/-- The only remaining numerical source input is the nonzero escaping-space
bound. Dimension and outside-overgroup generation are proved on this orbit.
Its discharge stays with the normalized Mathieu/J₄ assembly owner. -/
theorem sourceOrbit_mathieu_bounds_of_escaping_ranks
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hVW : V = D.sourceOrbit)
    (hm : Chapter7.NormalizedSource.HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hlocal : ∀ U : Subgroup G, U ≤ D.sourceOrbit → U ≠ ⊥ →
      ¬ centralizer (U : Set G) ≤ normalizer (L : Set G) →
        6 + rank U ≤ rank D.sourceOrbit) :
    globalW D.sourceOrbit (T : Subgroup G) ≤ 2 ∧ 6 ≤ globalR D.sourceOrbit :=
  D.sourceOrbit_mathieu_bounds_of_local_estimates h hmany hnon hVW
    ((by decide : 6 ≤ 10).trans (D.sourceOrbit_mathieu_rank_ge_ten hVW hm)) hlocal
    (fun _ hH => D.sourceOrbit_mathieu_generation_le_two_of_many h hmany hVW hm hnon hH)

/-- Literal M₂₃-code consumer with the dimension and generation premises
removed. The escaping-space estimate remains an explicit source obligation. -/
theorem sourceOrbit_not_m23Code_of_mathieu_escaping_ranks
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hVW : V = D.sourceOrbit)
    (hm : Chapter7.NormalizedSource.HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hlocal : ∀ U : Subgroup G, U ≤ D.sourceOrbit → U ≠ ⊥ →
      ¬ centralizer (U : Set G) ≤ normalizer (L : Set G) →
        6 + rank U ≤ rank D.sourceOrbit) :
    ¬ MathieuCode.IsM23Code (automizerRepresentation D.sourceOrbit) := by
  obtain ⟨hw, hr⟩ := D.sourceOrbit_mathieu_bounds_of_escaping_ranks h hmany hVW hm hnon hlocal
  exact D.sourceOrbit_not_m23Code_of_many h hmany hnon hw hr

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
