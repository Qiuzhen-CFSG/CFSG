module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Consequences
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit.SourceComplete
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesDefs
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.FixedSpace

/-!
# Chosen-seed inputs and the conditional structural consumer

The guard gives the proved local cubic bound. Nonzero fixed space gives
the original Thompson commutator with no common-normal or A.3.12 premise.
The normalizer-orbit cubic bound is stated separately on its literal action.

Reducedness of the Sylow orbit descends to the seed once that orbit equals
the seed. The two surviving source alternatives then give T-normalization,
reducedness, TI under N_G(L), and normalizer invariance or trivial fixed
space. The final consumer explicitly retains the source trichotomy and the
exclusion of its marked doubled alternative; neither is proved here.

Source: Aschbacher--Smith 3.2.5 and the structural prefix of12.2.2(3),
combined manuscript of 1 March 2004, printed pp.580 and794--795.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

 theorem sylowOrbit_reduced (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    IsPReduced 2 ((componentOrbit V (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))) := by
  have hr := ReducedNormal.subspaceImage_isPReduced_of_action_core
    (L ⊔ (T : Subgroup G)) D.orbitSpace (orbitSpan_invariant _ ⊤ D.space)
    (D.orbit_twoCore_eq_bot h)
  change IsPReduced 2 ((subspaceImage (L ⊔ (T : Subgroup G)) D.orbitSpace).subgroupOf
    (L ⊔ (T : Subgroup G))) at hr
  rwa [D.orbitSpace_image] at hr

 theorem reduced_of_sylow_normalizes (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hn : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    IsPReduced 2 (V.subgroupOf (L ⊔ (T : Subgroup G))) := by
  have he : componentOrbit V (T : Subgroup G) = V :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer V T V le_rfl hn) (le_componentOrbit V T)
  simpa only [he] using D.sylowOrbit_reduced h

 theorem structural_of_orbit_equalities_of_many (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (horbits : componentOrbit V (normalizer (L : Set G)) = V ∨
      (componentOrbit V (T : Subgroup G) = V ∧ V ⊓ centralizer (L : Set G) = ⊥)) :
    (T : Subgroup G) ≤ normalizer (V : Set G) ∧
    IsPReduced 2 (V.subgroupOf (L ⊔ (T : Subgroup G))) ∧
    (∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V) ∧
    ((normalizer (L : Set G)) ≤ normalizer (V : Set G) ∨
      V ⊓ centralizer (L : Set G) = ⊥) := by
  have hn : (T : Subgroup G) ≤ normalizer (V : Set G) := by
    rcases horbits with he | ⟨he,hc⟩
    · exact D.sylow_normalizes_component.trans (he ▸ le_normalizer_componentOrbit V (normalizer (L : Set G)))
    · exact he ▸ le_normalizer_componentOrbit V (T : Subgroup G)
  refine ⟨hn, D.reduced_of_sylow_normalizes h.toHypothesis1221 hn, ?_, ?_⟩
  · intro g hg
    rcases horbits with he | ⟨he,hc⟩
    · exact Or.inr (mem_normalizer_iff_map_conj_eq.mp
        ((he ▸ le_normalizer_componentOrbit V (normalizer (L : Set G))) hg))
    · exact D.ti_of_centralizer_eq_bot h.toHypothesis1221
        (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
        (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)) hc g hg
  · rcases horbits with he | ⟨he,hc⟩
    · exact Or.inl (he ▸ le_normalizer_componentOrbit V (normalizer (L : Set G)))
    · exact Or.inr hc

 theorem normalizerOrbit_elementary (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    IsElementaryAbelian 2 (componentOrbit V (normalizer (L : Set G))) := by
  have he := (D.fundamentalSetup h).fullModule_elementary_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  rwa [D.fundamentalSetup_fullModule] at he

/-- The still separate 3.1.6 numerical obligation uses the full normalizer
orbit and its literal faithful action, not the local-orbit representation. -/
def NormalizerOrbitCubicBound (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) : Prop :=
  letI := D.normalizerOrbit_elementary h
  cubicRatio (ChapterD.UniqueFactor.imageRepresentation (normalizer (L : Set G))
    (componentOrbit V (normalizer (L : Set G))) (le_normalizer_componentOrbit _ _)) ≤ 2

 theorem orbit_cubicRatio_le_of_many (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    cubicRatio D.orbitRepresentation ≤ 2 :=
  D.orbit_cubicRatio_le_source h.toHypothesis1221 (Chapter3.hasMaximalOutside_of_many T hmany)

/-- The fixed-space source branch yields the literal component commutator,
without an A.3.12 or common-normal callback. -/
theorem thompson_commutator_of_many_of_fixedSpace_ne_bot
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfix : V ⊓ centralizer (L : Set G) ≠ ⊥) :
    L = ⁅L, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
  have hf : (D.fundamentalSetup h.toHypothesis1221).seed ⊓
      centralizer (Chapter3.Section02.localOrbit T L : Set G) ≠ ⊥ := by
    rwa [D.fundamentalSetup_seed, D.localOrbit_eq]
  have he := ((D.fundamentalSetup h.toHypothesis1221).fixedSpace_consequences_of_many
    hmany hf).1
  rwa [D.localOrbit_eq] at he

/-- After the marked doubled branch has been excluded, the actual source
alternatives supply every chosen-module clause of the structural prefix.
The source alternatives and their exclusion remain explicit obligations. -/
theorem structural_of_source325_of_not_doubled_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (halt : D.Source325Alternatives) (hex : ¬ D.MarkedDoubled) :
    (T : Subgroup G) ≤ normalizer (V : Set G) ∧
    IsPReduced 2 (V.subgroupOf (L ⊔ (T : Subgroup G))) ∧
    (∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V) ∧
    ((normalizer (L : Set G)) ≤ normalizer (V : Set G) ∨
      V ⊓ centralizer (L : Set G) = ⊥) := by
  apply D.structural_of_orbit_equalities_of_many h hmany
  rcases halt with ⟨_,hU⟩ | ⟨hW,hc,_⟩ | hd
  · exact Or.inl hU
  · exact Or.inr ⟨hW,hc⟩
  · exact (hex hd).elim

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
