module

public import CFSG.Quasithin.ChapterD.Section03.InternalKernel
public import CFSG.Quasithin.ChapterD.Section03.InternalCoreImage
public import CFSG.Quasithin.ChapterD.Section03.SourceConsequences

/-!
# The faithful internal orbit module: D.3.3

Starting with the linear action of the original internal elementary
section, restrict to the actual orbit span of its seed and pass to the
literal action image. The seed stays Irr⁺ and generates this whole
module. Both actor alternatives descend, and the actor kernel lies
between its two-core and core–Frattini subgroup. Exact two-core transfer
on X T proves the last seed-invariance condition of D.3.1.

The original SQTK group and the actual action kernel provide the covering
quotient. No faithful-image, kernel-bound, or core-invariance conclusion
is retained as an additional premise.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma D.3.3, printed p.193.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.ChapterD.Section03
universe u
variable {G V : Type u} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K : GroupClass.{u}}
  {T : Sylow 2 G} {X : Subgroup G} {I : Submodule (ZMod 2) V}

/-- D.3.3(1): the actual faithful orbit action satisfies all of D.3.1. -/
theorem InternalModuleHypotheses.faithfulOrbit_source
    (h : InternalModuleHypotheses K ρ T X I) :
    SourceHypotheses K (subspaceImageRepresentation ρ (orbitSpan ρ ⊤ I))
      (T.mapSurjective (invariantActionHom_surjective ρ _ (orbitSpan_invariant ρ ⊤ I)))
      (restrictedSubgroup ρ (orbitSpan ρ ⊤ I) X)
      (I.comap (orbitSpan ρ ⊤ I).subtype) := by
  let := h.finiteModule
  let := h.normal
  let W := orbitSpan ρ ⊤ I
  let f := invariantActionHom ρ W (orbitSpan_invariant ρ ⊤ I)
  have hf : Function.Surjective f := invariantActionHom_surjective ρ W _
  have hm (A : Subgroup G) : A.map f = restrictedSubgroup ρ W A :=
    invariantActionHom_map ρ W _ A
  have hn : (restrictedSubgroup ρ W X).Normal := by
    rw [← hm X]
    exact Normal.map inferInstance f hf
  have hTX : (T : Subgroup G) ≤ normalizer (X : Set G) := by
    rw [normalizer_eq_top]
    exact le_top
  have hk : X ⊓ f.ker ≤ (coreFrattiniIn X).map X.subtype := by
    intro x hx
    apply h.orbit_actorKernel_le_coreFrattini
    rw [invariantActionHom_ker] at hx
    exact ⟨hx.1, hx.2.2⟩
  have hcover : Nonempty (ChapterB.SourceInduction.SQTKQuotient K
      (subspaceActionImage ρ W)) := ⟨{
    Cover := G
    kernel := f.ker
    sqtk := h.sqtk
    equiv := QuotientGroup.quotientKerEquivOfSurjective f hf }⟩
  refine ⟨hcover, inferInstance, subspaceImageRepresentation_injective ρ W, hn, ?_,
    isIrrPlus_faithfulOrbit ρ h.seed, ?_, orbitSpan_faithfulOrbit_eq_top ρ I⟩
  · have hbar : (T.mapSurjective hf : Subgroup (subspaceActionImage ρ W)) ≤
        normalizer (X.map f : Set _) := by
      let : (X.map f).Normal := Normal.map inferInstance f hf
      rw [normalizer_eq_top]
      exact le_top
    have hc : ActorCases (T.mapSurjective hf) (X.map f) hbar := by
      rcases h.cases with ⟨L, hL, hq, hLX⟩ | ⟨p, hp, ho, hP, hIr⟩
      · exact Or.inl (component_internal_actor_image hL hq hLX f hf
          h.orbitMap_kills_core (by rw [hm]; exact h.orbit_actor_ne_bot))
      · exact actorCases_of_internal_odd_image f hf T X hTX h.orbitMap_kills_core
          hp ho hP hIr hbar
    simpa only [hm] using hc
  · have he := map_join_twoCore_of_internal_kernel f X (T : Subgroup G) hTX
      h.residual T.isPGroup' hk
    change (restrictedSubgroup ρ W X ⊔ (T : Subgroup G).map f).pCoreIn 2 ≤ _
    rw [← hm X, ← he, hm]
    exact faithfulOrbit_seed_stabilized ρ I h.coreInvariant

/-- D.3.3(2): both inclusions for the literal actor kernel on the orbit module. -/
theorem InternalModuleHypotheses.orbit_actorKernel_bounds
    (h : InternalModuleHypotheses K ρ T X I) :
    X.pCoreIn 2 ≤ subspaceKernel ρ (orbitSpan ρ ⊤ I) X ∧
      subspaceKernel ρ (orbitSpan ρ ⊤ I) X ≤ (coreFrattiniIn X).map X.subtype := by
  refine ⟨?_, h.orbit_actorKernel_le_coreFrattini⟩
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x.property, fun v _ => h.actorCore_fixes x hx v⟩

/-- The faithful internal image therefore has trivial two-core, by D.3.4(1). -/
theorem InternalModuleHypotheses.faithfulOrbit_twoCore_eq_bot
    (h : InternalModuleHypotheses K ρ T X I) :
    pCore 2 (subspaceActionImage ρ (orbitSpan ρ ⊤ I)) = ⊥ :=
  h.faithfulOrbit_source.twoCore_eq_bot

end CFSG.Quasithin.ChapterD.Section03
