module
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuInitialBounds
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGlobalBounds
public import Theory.Representation.BinaryOffender.SylowTransport
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.SourceCompleteBound

/-!
# Initial weak-closure bounds on the normalized Mathieu orbit

The faithful LT action has Sylow-containing image in Aut_G(W). Sylow
conjugacy transfers the actual marked involution bound to that full
ambient automizer. E.6.3 gives r ≥ m > 2 and s = m; the completed outside
H* generation cap then gives w ≤ n(H) ≤ 2 < s, on the original orbit.
No rank, generation, Held-cover, or action-transport premise is retained.

The private import intentionally continues Actor.Orbit: the local transport
uses the literal quotient action formula. The analogous public transport in
NonFFSourceNonMathieuRankOneUnitaryParameters cannot be imported together
with MathieuGeneration because their dependency chains currently export the
same sourceOrbit_hstar_centralizes_omega name. This local proof leaves those
independently owned APIs untouched.

The stronger escaping-space estimates, shadow eliminations and final J₄
recognition remain with the normalized Mathieu assembly.
Source: Aschbacher--Smith, E.6.3 and 7.3.2--4, printed pp.245,698--699.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterE.Section06 Chapter7.NormalizedSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The literal LT orbit action embeds equivariantly in the ambient automizer,
and its image contains the Sylow induced by the original T. -/
private theorem mathieu_actor_automizer_marking :
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


/-- Sylow conjugacy transfers the marked Mathieu bound to the literal full
ambient automizer, even when LT has a proper image in that automizer. -/
theorem sourceOrbit_mathieu_localM_ge_three
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hm : HasMathieuCentralQuotient D.orbitComponent) :
    3 ≤ localM D.sourceOrbit := by
  have hm' := mathieu_moduleM_ge_three D.orbitRepresentation D.orbitComponent hs hm
  apply le_csInf ⟨_, Set.mem_insert _ _⟩
  rintro d (rfl | ⟨t,ht,rfl⟩)
  · exact hm'.trans ((moduleM_le_dimension _).trans D.sourceOrbitCoordinates.finrank_eq.le)
  · have hA : IsElementaryTwo (zpowers t) :=
      ⟨fun hb => by
          have ht1 := mem_bot.mp (hb ▸ mem_zpowers t)
          simp [ht1] at ht,
        IsElementaryAbelian.zpowers_of_pow_eq_one ((orderOf_eq_prime_iff.mp ht).1)⟩
    obtain ⟨f,hf,he,S,hS⟩ := D.mathieu_actor_automizer_marking
    obtain ⟨B,hB,_,hc⟩ := elementary_geometry_of_sylow_range
      D.orbitRepresentation (automizerRepresentation D.sourceOrbit)
      f hf D.sourceOrbitCoordinates he S hS _ hA
    exact hc ▸ hm'.trans (moduleM_le_fixedCodim _ hB)

/-- Source 7.3.2 on the actual normalized Mathieu orbit, with every model
premise of E.6.3 discharged. -/
theorem sourceOrbit_mathieu_initial_parameters
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hVW : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    (localM D.sourceOrbit : ℕ∞) ≤ globalR D.sourceOrbit ∧
      globalS D.sourceOrbit = (localM D.sourceOrbit : ℕ∞) ∧
      2 < globalS D.sourceOrbit :=
  FrobeniusReduction.lower_bound_knownSimple
    (D.sourceOrbit_hypothesisE61_of_many h hmany hnon hVW)
    (D.sourceOrbit_mathieu_localM_ge_three
      (D.sourceOrbit_chapterK_of_many h hmany hnon hVW) hm)

/-- Source 7.3.4: the actual normalized Mathieu orbit has w ≤ 2. -/
theorem sourceOrbit_mathieu_globalW_le_two
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hVW : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    globalW D.sourceOrbit (T : Subgroup G) ≤ 2 := by
  have hr := (D.sourceOrbit_mathieu_initial_parameters h hmany hVW hm hnon).1
  have hm' : (2 : ℕ∞) < (localM D.sourceOrbit : ℕ∞) := by
    exact_mod_cast D.sourceOrbit_mathieu_localM_ge_three
      (D.sourceOrbit_chapterK_of_many h hmany hnon hVW) hm
  exact D.sourceOrbit_mathieu_globalW_le_two_of_globalR h hmany hVW hm hnon (hm'.trans_le hr)

/-- The complete initial source 7.3.4 inequalities hold for every original
outside H*, with its literal E-generation parameter. -/
theorem sourceOrbit_mathieu_generation_bounds
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hVW : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    globalW D.sourceOrbit (T : Subgroup G) ≤ (generationParameter H : ℕ∞) ∧
      generationParameter H ≤ 2 ∧
      (generationParameter H : ℕ∞) < globalS D.sourceOrbit := by
  have hb := D.sourceOrbit_mathieu_generation_le_two_of_many h hmany hVW hm hnon hH
  have hb' : (generationParameter H : ℕ∞) ≤ 2 := by exact_mod_cast hb
  obtain ⟨hr,hS,hpos⟩ := D.sourceOrbit_mathieu_initial_parameters h hmany hVW hm hnon
  have hsr : globalS D.sourceOrbit ≤ globalR D.sourceOrbit := by rw [hS]; exact hr
  refine ⟨?_,hb,hb'.trans_lt hpos⟩
  exact (min_le_iff.mp (D.sourceOrbit_min_parameters_le_generation h hH)).resolve_right
    (not_le_of_gt ((hb'.trans_lt hpos).trans_le hsr))
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
