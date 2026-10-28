module
public import CFSG.Quasithin.Chapter3.Section02.SourceSelection

/-!
# Choosing a minimal original full module

The fundamental setup can be chosen with smallest full-module order while
keeping the ambient group, Sylow subgroup and component fixed. Any valid
reselection whose full module is contained in this one then has the same
full module. This is the finite descent needed for the new choice of seed
in the two-natural-module alternative D.3.21(3).

This module proves the choice and its strict-descent obstruction. It does
not assert that the D.3.21 replacement exists or that tensor modules have
been excluded. Those are distinct source implications.
Source: Aschbacher–Smith,D.3.21 and the proof of3.2.6,
printed pp.204–207 and581.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter3.Section02.FundamentalSetup
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  {T : Sylow 2 G} {L : Subgroup G}

/-- Minimality among the actual setups with the same original G, T and L. -/
def IsMinimalFullModule (D : FundamentalSetup K T L) : Prop :=
  ∀ E : FundamentalSetup K T L, Nat.card D.fullModule ≤ Nat.card E.fullModule

/-- An existing original setup can be reselected with minimal full module. -/
theorem exists_minimal_fullModule (D : FundamentalSetup K T L) :
    ∃ E : FundamentalSetup K T L, E.IsMinimalFullModule := by
  classical
  let P : ℕ → Prop := fun n => ∃ E : FundamentalSetup K T L, Nat.card E.fullModule = n
  have hex : ∃ n, P n := ⟨Nat.card D.fullModule,D,rfl⟩
  obtain ⟨E,hE⟩ := Nat.find_spec hex
  refine ⟨E,fun F => ?_⟩
  rw [hE]
  exact Nat.find_min' hex ⟨F,rfl⟩

/-- A replacement cannot have a proper smaller full module. -/
theorem IsMinimalFullModule.eq_of_le {D : FundamentalSetup K T L}
    (hD : D.IsMinimalFullModule) (E : FundamentalSetup K T L)
    (hE : E.fullModule ≤ D.fullModule) : E.fullModule = D.fullModule := by
  exact Subgroup.eq_of_le_of_card_ge hE (hD E)

/-- The strict-descent form used to remove the two-natural alternative. -/
theorem IsMinimalFullModule.not_lt {D : FundamentalSetup K T L}
    (hD : D.IsMinimalFullModule) (E : FundamentalSetup K T L) :
    ¬ E.fullModule < D.fullModule := by
  intro hE
  exact hE.ne (hD.eq_of_le E hE.le)

/-- The original source hypotheses construct a minimal setup directly. -/
theorem exists_minimal_fullModule_of_source
    (hG : IsSimpleQTKE K G) (hL : L ∈ Chapter1.LStar G (T : Subgroup G))
    (hf : ChapterA.Section04.IsFaithfulSignalizerType L)
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) :
    ∃ D : FundamentalSetup K T L, D.IsMinimalFullModule := by
  obtain ⟨D⟩ := source_exists_fundamentalSetup hG T L hL hf hq
  exact D.exists_minimal_fullModule

/-- An actual Irr⁺ subspace inside an M-invariant subgroup supplies a new
fundamental setup whose full orbit stays in that subgroup. -/
theorem exists_reselection_fullModule_le (D : FundamentalSetup K T L)
    (I : Submodule (ZMod 2) (Additive (ReducedNormal.ModuleGroup (localJoin T L))))
    (hI : IsIrrPlus (ReducedNormal.representation (localJoin T L))
      ((localOrbit T L).subgroupOf (localJoin T L)) I)
    (U : Subgroup G) (hIU : ReducedNormal.subspaceImage (localJoin T L) I ≤ U)
    (hU : D.maximalLocal ≤ normalizer (U : Set G)) :
    ∃ E : FundamentalSetup K T L, E.fullModule ≤ U := by
  obtain ⟨E, hEI, _⟩ := lemma_3_2_3_constituent D.simpleQTKE T L D.maximal
    D.faithful D.quasisimple I hI
  have hTU : (T : Subgroup G) ≤ normalizer (U : Set G) :=
    (le_normalizer_componentOrbit L T).trans hU
  have hEU : E.seed ≤ U := by
    have hs := ReducedNormal.subspaceImage_mono (localJoin T L) hEI
    rw [ReducedNormal.subspaceImage_orbitSpan _ _ le_sup_right] at hs
    exact hs.trans (iSup_conjugates_le_of_le_normalizer _ _ _ hIU hTU)
  refine ⟨E, ?_⟩
  rw [E.fullModule_eq_seed_orbit]
  exact iSup_conjugates_le_of_le_normalizer _ _ _ hEU hU

/-- Minimality rules out a proper M-invariant subgroup that contains an
actual reduced Irr⁺ constituent; no preconstructed replacement setup is needed. -/
theorem IsMinimalFullModule.eq_of_contains_irrPlus
    {D : FundamentalSetup K T L} (hD : D.IsMinimalFullModule)
    (I : Submodule (ZMod 2) (Additive (ReducedNormal.ModuleGroup (localJoin T L))))
    (hI : IsIrrPlus (ReducedNormal.representation (localJoin T L))
      ((localOrbit T L).subgroupOf (localJoin T L)) I)
    (U : Subgroup G) (hIU : ReducedNormal.subspaceImage (localJoin T L) I ≤ U)
    (hU : D.maximalLocal ≤ normalizer (U : Set G)) (hUD : U ≤ D.fullModule) :
    U = D.fullModule := by
  obtain ⟨E,hE⟩ := D.exists_reselection_fullModule_le I hI U hIU hU
  have he := hD.eq_of_le E (hE.trans hUD)
  exact le_antisymm hUD (he ▸ hE)

end CFSG.Quasithin.Chapter3.Section02.FundamentalSetup
