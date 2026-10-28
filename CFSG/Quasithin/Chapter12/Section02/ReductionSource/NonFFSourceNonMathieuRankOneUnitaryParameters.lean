module
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuRankOneGeneration
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuRankOneUnitaryGeometry
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuRankOneOddCodimension

/-!
# Initial unitary parameters and the ambient centralizer reduction

The faithful LT action embeds into the literal automizer and contains the
Sylow image of the original T. Sylow conjugacy therefore transfers the
natural unitary elementary geometry to every ambient elementary actor.
This proves the local m bound, the initial E.6.3 bounds, and higher-Thompson
control. Completed odd-local control then applies E.6.27.

The final r bound and exclusion here retain the two genuine remaining model
estimates: odd-prime displacement under the ambient SQTK cover, and the
Cartan bound on the literal quotient-action image. Their discharge remains
with qt-d-1222-nonmathieu-unitary-suzuki-exclusion. These conditional exports
do not assert the final unitary source exclusion.

The private import is an intentional continuation of Actor.Orbit to check
the original quotient map's conjugation formula; it changes no public API.
Source: Aschbacher--Smith H.2, 7.2.1--7.5.2 and E.6.27,
printed pp.378,698--700,257.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB ChapterE ChapterE.Section06 ChapterE.Section06.FixedPointBounds Chapter7.NormalizedSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The literal LT orbit action embeds equivariantly in the ambient automizer,
and its image contains the Sylow induced by the original T. -/
theorem sourceOrbit_actor_automizer_marking :
    ∃ f : D.orbitActor →* Automizer D.sourceOrbit,
      Function.Injective f ∧
      (∀ a v, D.sourceOrbitCoordinates (D.orbitRepresentation a v) =
        automizerRepresentation D.sourceOrbit (f a) (D.sourceOrbitCoordinates v)) ∧
      ∃ S : Sylow 2 (Automizer D.sourceOrbit), (S : Subgroup _) ≤ f.range := by
  let H := L ⊔ (T : Subgroup G)
  have hHN : H ≤ normalizer (D.sourceOrbit : Set G) :=
    sup_le D.sourceOrbit_component_normalizes D.sourceOrbit_weakClosure_setup.normalizes
  let q := D.sourceOrbit.normalizerMonoidHom.rangeRestrict
  let k : H →* Automizer D.sourceOrbit := q.comp (inclusion hHN)
  have hk (g : H) (v : D.orbitSpace) :
      D.sourceOrbitCoordinates (D.orbitRepresentation (D.orbitHom g) v) =
        automizerRepresentation D.sourceOrbit (k g) (D.sourceOrbitCoordinates v) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (D.sourceOrbitCoordinates_apply (D.orbitRepresentation (D.orbitHom g) v)).trans
      (congrArg (fun x : G => (g : G) * x * (g : G)⁻¹)
        (D.sourceOrbitCoordinates_apply v).symm)
  obtain ⟨f,hfi,he,hf⟩ := faithful_action_factor D.orbitRepresentation
    (automizerRepresentation D.sourceOrbit) (subspaceImageRepresentation_injective _ _)
    (automizerRepresentation_injective D.sourceOrbit) D.orbitHom D.orbitHom_surjective
    k D.sourceOrbitCoordinates hk
  refine ⟨f,hfi,he,?_,?_⟩
  · exact (T.subtype D.sourceOrbit_weakClosure_setup.normalizes).mapSurjective
      D.sourceOrbit.normalizerMonoidHom.rangeRestrict_surjective
  · rintro _ ⟨t,ht,rfl⟩
    refine ⟨D.orbitHom ⟨t,mem_sup_right ht⟩,?_⟩
    rw [hf]
    rfl

/-- Both local unitary estimates on every actual elementary automizer actor. -/
theorem sourceOrbit_unitary_elementary_geometry
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2^s))
    (A : Subgroup (Automizer D.sourceOrbit)) (hA : IsElementaryTwo A) :
    2*s ≤ fixedCodim (automizerRepresentation D.sourceOrbit) A ∧
      rank A + 1 < fixedCodim (automizerRepresentation D.sourceOrbit) A := by
  obtain ⟨f,hf,he,S,hS⟩ := D.sourceOrbit_actor_automizer_marking
  obtain ⟨B,hB,hr,hc⟩ := elementary_geometry_of_sylow_range
    D.orbitRepresentation (automizerRepresentation D.sourceOrbit)
    f hf D.sourceOrbitCoordinates he S hS A hA
  obtain ⟨F,_,_,_,J,hcard,hconj,⟨M⟩,_⟩ := D.sourceOrbit_unitary_model hs hs2 hq
  have hb := unitary_elementary_geometry hs M hs2 hcard hconj B hB
  rwa [hr,hc] at hb

/-- The unitary local involution parameter, on the literal automizer. -/
theorem sourceOrbit_unitary_localM
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2^s)) :
    2*s ≤ localM D.sourceOrbit := by
  apply le_csInf ⟨_, Set.mem_insert _ _⟩
  rintro d (rfl | ⟨t,ht,rfl⟩)
  · obtain ⟨_,_,_,_,_,_,_,_,hd⟩ := D.sourceOrbit_unitary_model hs hs2 hq
    rw [hd]
    omega
  · have hA : IsElementaryTwo (zpowers t) :=
      ⟨fun hb => by
          have ht1 := mem_bot.mp (hb ▸ mem_zpowers t)
          simp [ht1] at ht,
        IsElementaryAbelian.zpowers_of_pow_eq_one ((orderOf_eq_prime_iff.mp ht).1)⟩
    exact (D.sourceOrbit_unitary_elementary_geometry hs hs2 hq _ hA).1

/-- Source 7.3.2 with the genuine Held-cover theorem already discharged. -/
theorem sourceOrbit_unitary_initial_parameters
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2^s)) :
    ((2*s : ℕ) : ℕ∞) ≤ globalR D.sourceOrbit ∧
      globalS D.sourceOrbit = (localM D.sourceOrbit : ℕ∞) ∧ 2 < globalS D.sourceOrbit := by
  have hlocal := D.sourceOrbit_unitary_localM hs hs2 hq
  obtain ⟨hr,hS,hpos⟩ := FrobeniusReduction.lower_bound_knownSimple
    (D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon) (by omega)
  exact ⟨(ENat.natCast_le_natCast.mpr hlocal).trans hr,hS,hpos⟩

/-- Every higher-Thompson generator centralizes the original unitary orbit. -/
theorem sourceOrbit_unitary_thompson_one_centralizes
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2^s))
    (X : Subgroup G) (hWX : D.sourceOrbit ≤ X)
    (hXN : X ≤ normalizer (D.sourceOrbit : Set G)) :
    thompsonJ X 1 ≤ centralizer (D.sourceOrbit : Set G) :=
  thompson_centralizes_of_fixedCodim_gap D.sourceOrbit X hWX hXN
    (fun A hA => (D.sourceOrbit_unitary_elementary_geometry hs hs2 hq A hA).2)

/-- E.6.27 with the initial and higher-Thompson bounds discharged. -/
theorem sourceOrbit_unitary_centralizer_le_of_nPrime
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2^s))
    {U : Subgroup G} (hU : U ≠ ⊥) (hUW : U ≤ D.sourceOrbit)
    (hn : nPrime (inducedAutomizer D.sourceOrbit
      (normalizer (L : Set G) ⊓ centralizer (U : Set G))) ≤ 1) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) := by
  have hr := (D.sourceOrbit_unitary_initial_parameters h hmany hV hs hnon hs2 hq).1
  have h61 := D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon
  apply D.sourceOrbit_unitary_centralizer_le h hmany hV hs hnm hnon hs2 hq hU hUW (by decide) ?_ hn ?_
  · exact lt_of_lt_of_le (by exact_mod_cast (show 1 < 2*s by omega)) hr
  · exact le_inf (thompsonJ_le _ _ |>.trans inf_le_left)
      (D.sourceOrbit_unitary_thompson_one_centralizes hs hs2 hq _
        (h61.normal_in_localCentralizer hU hUW).1 (h61.localCentralizer_le_normalizer hU hUW))

/-- The full ambient r-bound from the remaining SQTK-dependent H.2 estimate.
That estimate is retained with this module's final source assembly owner. -/
theorem sourceOrbit_unitary_globalR_of_odd_fixedCodim
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2^s))
    (hodd : ∀ (p : ℕ), p.Prime → Odd p → ∀ a : Automizer D.sourceOrbit,
      orderOf a = p → 4*s ≤ fixedCodim (automizerRepresentation D.sourceOrbit) (zpowers a)) :
    ((4*s : ℕ) : ℕ∞) ≤ globalR D.sourceOrbit := by
  by_cases ht : globalR D.sourceOrbit = ⊤
  · simp [ht]
  obtain ⟨U,hUW,hescape,hcor⟩ := globalR_attained ht
  rw [←hcor]
  apply ENat.natCast_le_natCast.mpr
  by_contra hn
  have hc : subgroupCorank D.sourceOrbit U < 4*s := by omega
  have hU : U ≠ ⊥ := by
    intro hz
    obtain ⟨_,_,_,_,_,_,_,_,hd⟩ := D.sourceOrbit_unitary_model hs hs2 hq
    rw [hz,corank_bot,hd] at hc
    omega
  have h61 := D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon
  apply hescape ((h61.centralizer_le_iff hU hUW).mp ?_)
  apply D.sourceOrbit_unitary_centralizer_le_of_nPrime h hmany hV hs hnm hnon hs2 hq hU hUW
  exact induced_nPrime_le_one_of_odd_fixedCodim D.sourceOrbit _ U
    (h61.localCentralizer_le_normalizer hU hUW) hUW inf_le_right
    (b := 4*s) (c := 1) (by simpa using hodd) (by simpa using hc)

/-- The weak Cartan bound 2s already suffices for the unitary FWCI endgame.
Both remaining model estimates must be proved by the same final owner. -/
theorem sourceOrbit_unitary_excluded_of_model_estimates
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2^s))
    (hcartan : nPrime (normalizerPCoreQuotientAction L).range ≤ 2*s)
    (hodd : ∀ (p : ℕ), p.Prime → Odd p → ∀ a : Automizer D.sourceOrbit,
      orderOf a = p → 4*s ≤ fixedCodim (automizerRepresentation D.sourceOrbit) (zpowers a)) : False := by
  have hr := D.sourceOrbit_unitary_globalR_of_odd_fixedCodim h hmany hV hs hnm hnon hs2 hq hodd
  have hb := (D.sourceOrbit_unitary_min_parameters_le_nPrime h hmany hV hs hnm hnon hs2 hq).trans
    (ENat.natCast_le_natCast.mpr hcartan)
  have hlt : ((2*s : ℕ) : ℕ∞) < globalR D.sourceOrbit :=
    lt_of_lt_of_le (by exact_mod_cast (show 2*s < 4*s by omega)) hr
  have hw := (min_le_iff.mp hb).resolve_right (not_le_of_gt hlt)
  exact Chapter7.impossible_parameter_bounds D.sourceOrbit_weakClosure_setup
    (D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon)
    (D.sourceOrbit_unitary_automizer_rank h hs hs2 hq) hw hr (by omega)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
