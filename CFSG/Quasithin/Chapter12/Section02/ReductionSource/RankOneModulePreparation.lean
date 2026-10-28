module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleInputs
public import CFSG.Quasithin.ChapterA.Section04.Modules

/-!
# Preparing the literal Chapter 6 hypotheses on the whole reduced subgroup

The two local-family definitions agree, including relative C-component
membership and maximality. The two omega-center conventions also agree.
Reducedness is used only for R₂(LT), and nontriviality of its commutator
layer follows from the original chosen section. Thus the source 6.1.1
configuration is available once the numerical branch and failure of the
A₅-module exit have been established; no property of the chosen V is
silently substituted for a property of the whole reduced subgroup.

Source: Aschbacher--Smith, 6.1.1 and 12.2.2, pp.663 and 795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem centralOmega_eq (Q : Subgroup G) :
    Chapter6.Source.centralOmega Q = Stellmacher.omegaOneCenterAmbient Q := by
  apply le_antisymm
  · apply (omegaOneAmbient_le_iff _ _).mpr
    intro x hx hp
    exact (Stellmacher.mem_omegaOneCenterAmbient_iff Q x).mpr
      ⟨hx.1, hp, mem_centralizer_iff.mp hx.2⟩
  · intro x hx
    obtain ⟨hxQ, hp, hc⟩ := (Stellmacher.mem_omegaOneCenterAmbient_iff Q x).mp hx
    exact (omegaOneAmbient_le_iff _ _).mp le_rfl x
      ⟨hxQ, mem_centralizer_iff.mpr hc⟩ hp

/-- Canonical Chapter 12 local membership supplies the original Chapter 6 family. -/
theorem faithfulMaximalFamily_of_hypothesis
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    L ∈ Chapter6.Source.faithfulMaximalFamily (T : Subgroup G) := by
  refine ⟨⟨h.maximal_faithful.1.1, ?_⟩, ?_⟩
  · intro J hJ hLJ
    exact (h.maximal_faithful.1.2 J hJ hLJ).le
  · refine ⟨h.maximal_faithful.2.1.1, h.maximal_faithful.2.1.2.1,
      h.maximal_faithful.2.1.2.2, ?_⟩
    rw [centralOmega_eq, commutator_comm]
    simpa only [Subgroup.pCoreIn, ChapterA.Section04.intrinsicSignalizerModule,
      ChapterA.Section04.signalizerModule_eq_commutator_omegaCenter] using
      h.maximal_faithful.2.2

omit [Finite G] in
/-- The entire R₂(LT), with the original inclusion, belongs to the source
reduced family. This makes no assertion about the selected V's reducedness. -/
theorem wholeReduced_mem :
    wholeReduced T L ∈ Chapter6.Source.reducedFamily (L ⊔ (T : Subgroup G)) := by
  let H := L ⊔ (T : Subgroup G)
  have he : (wholeReduced T L).subgroupOf H = ReducedModule H := by
    change ((ReducedModule H).map H.subtype).comap H.subtype = _
    exact comap_map_eq_self_of_injective H.subtype_injective _
  refine ⟨map_subtype_le _, ?_, ?_⟩
  · exact IsElementaryAbelian.map _
  · have hr : IsPReduced 2 ((wholeReduced T L).subgroupOf H) :=
      he.symm ▸ isPReduced_reducedPSubgroup
    exact ⟨hr.normal, hr.quotient_pCore_eq_bot⟩

/-- The normalizer in the source 6.1.1 configuration is an actual maximal
local, with L normal relative to that subgroup. -/
theorem normalizer_configuration (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    IsMaximalTwoLocal (normalizer (L : Set G)) ∧
      (T : Subgroup G) ≤ normalizer (L : Set G) ∧
      (L.subgroupOf (normalizer (L : Set G))).Normal := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have he : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L T L le_rfl
      D.sylow_normalizes_component) (le_componentOrbit L T)
  exact ⟨he ▸ hu.normalizer_maximal, D.sylow_normalizes_component,
    normal_subgroupOf_of_le_normalizer le_rfl⟩

/-- All literal 6.1.1 inputs except its numerical and module-case assumptions
are supplied by the actual Chapter 12 configuration. -/
theorem hypothesis611 (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hgen : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      ChapterE.generationParameter H = 1)
    (hmodel : ¬ Chapter6.Source.IsOneOrTwoA5Modules L (commutatorLayer T L)) :
    Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n := by
  obtain ⟨hM, hTM, hLM⟩ := normalizer_configuration D h
  exact ⟨h.simpleQTKE, faithfulMaximalFamily_of_hypothesis h, hpsl, hn,
    hM, hTM, L.le_normalizer, hLM, wholeReduced_mem,
    D.rankOne_commutatorLayer_ne_bot, hmodel, hgen⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
