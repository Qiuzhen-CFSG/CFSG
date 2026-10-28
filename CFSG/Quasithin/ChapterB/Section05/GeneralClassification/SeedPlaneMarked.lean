module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SeedPlaneActor
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Comparison.ModelFacts.Doubled.SeedGeneration
public import Theory.Representation.BinaryOffender.NoncentralMoved
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.ComponentPlaneComplete

/-!
# Retaining the marked B.5 component seed

The faithful prepared seed is an invariant subspace of the component moved
space. Irr⁺ makes every proper invariant subspace central; faithfulness on
the nontrivial component excludes that alternative. Thus the seed is the
literal moved space. The complete B.5 source conclusion is retained with
its action rather than discarded after extracting the carrier catalogue.

Source: Aschbacher–Smith, B.5.9 and 13.7.18, printed pp.107 and945.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction
open QuasisimpleSource ComponentReduction ComponentReduction.PreliminaryActions
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem seed_eq_moved_of_irrPlus {K : GroupClass.{u}} {A L : Subgroup G}
    (hLA : ⁅L,A⁆ = L) (p : Prepared ρ K hLA) (hL : IsComponent G L)
    (hi : IsIrrPlus ρ L (moved ρ L)) : naturalSeedSpace ρ L A = moved ρ L := by
  rcases hi.eq_or_le_fixedSpace ρ
    (le_sup_left.trans (seedSpace_stable ρ hLA)) (seedSpace_le_moved ρ A L) with he | hc
  · exact he
  · have ht : ∀ l : L, l = 1 := by
      intro l
      apply p.component_faithful
      apply LinearMap.ext
      intro w
      apply Subtype.ext
      exact (hc w.property l).trans (by simp)
    have hb : L = ⊥ := by
      apply bot_unique
      intro l hl
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val (ht ⟨l,hl⟩))
    let : IsQuasisimple L := hL.2
    let : IsSimpleGroup (L ⧸ center L) := hL.2.simple
    let : Nontrivial L := Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (center L))
    have hn : L ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot L).mp inferInstance
    exact (hn hb).elim

private theorem componentMarkInput : Preparation.ComponentInput.{u,v} KnownSimple.IsKnownSimple :=
  PreparationSource.componentInput_of_classification_sources
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
    SourceClassification.irreducibleClassification_knownSimple

private theorem quasisimpleMarkInput :
    ProjectiveLine.QuasisimpleClassificationInput.{u,v} KnownSimple.IsKnownSimple :=
  QuasisimpleSource.SourceCompletion.knownSimple_quasisimpleClassificationInput
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
    SourceClassification.irreducibleClassification_knownSimple nonbinaryG2RootPairInput

theorem ff_component_marked_seed [FiniteDimensional (ZMod 2) V]
    (hyp : FFHypothesis KnownSimple.IsKnownSimple ρ)
    {L A : Subgroup G} (hL : IsComponent G L) (hA : IsMinimalBestOffender ρ A)
    (hLA : ⁅L,A⁆ = L) (hi : IsIrrPlus ρ L (moved ρ L)) :
    ∃ _p : Prepared ρ KnownSimple.IsKnownSimple hLA,
      Nonempty (ProjectiveLine.QuasisimpleSourceConclusion
        (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA)) ∧
      naturalSeedSpace ρ L A = moved ρ L ∧
      moved (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA) = ⊤ := by
  have hs := PreparationSource.component_sqtk ρ
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple) hyp hL
  have p := Preparation.prepared_of_component_rank ρ componentMarkInput hyp hA hL hLA
    hs.stronglyQuasithin
  exact ⟨p, quasisimpleMarkInput _ _ _ _ p.source,
    seed_eq_moved_of_irrPlus ρ hLA p hL hi, seedQuotient_moved_eq_top ρ hLA hL⟩


/-- Minimal-plane application retaining the actual restricted offender actor,
its prepared seed, and the complete marked B.5 conclusion. -/
theorem component_marked_seed_of_minimal_plane [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    (cover : SQTKQuotient KnownSimple.IsKnownSimple G)
    {L A : Subgroup G} (hL : IsComponent G L) (hA : IsMinimalBestOffender ρ A)
    (hLA : ⁅L,A⁆ = L) (hd : Module.finrank (ZMod 2) (moved ρ A) ≤ 2) :
    let N := offenderSubgroup ρ
    ∃ (_hLN : L ≤ N) (_hAN : A ≤ N),
      ∃ hcomm : ⁅L.subgroupOf N,A.subgroupOf N⁆ = L.subgroupOf N,
        ∃ _p : Prepared (ρ.comp N.subtype) KnownSimple.IsKnownSimple hcomm,
          Nonempty (ProjectiveLine.QuasisimpleSourceConclusion
            (seedQuotientAction (ρ.comp N.subtype) hcomm)
            (seedComponentImage (ρ.comp N.subtype) hcomm)) ∧
          naturalSeedSpace (ρ.comp N.subtype) (L.subgroupOf N) (A.subgroupOf N) =
            moved (ρ.comp N.subtype) (L.subgroupOf N) ∧
          moved (seedQuotientAction (ρ.comp N.subtype) hcomm)
            (seedComponentImage (ρ.comp N.subtype) hcomm) = ⊤ := by
  let N := offenderSubgroup ρ
  have hAN : A ≤ N := hA.1.le_offenderSubgroup ρ
  obtain ⟨hLN,_,hLNs⟩ := moved_component_in_offenderSubgroup ρ hf hL hA.1 hLA
  have hA₀ : IsMinimalBestOffender (ρ.comp N.subtype) (A.subgroupOf N) := by
    let : IsElementaryAbelian 2 A := hA.1.1.2
    apply Preparation.minimal_of_injective_image ρ N.subtype N.subtype_injective
      (IsElementaryAbelian.subgroupOf hAN)
    rwa [map_subgroupOf_eq_of_le hAN]
  have hcomm : ⁅L.subgroupOf N,A.subgroupOf N⁆ = L.subgroupOf N := by
    apply map_injective N.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hLN,map_subgroupOf_eq_of_le hAN,hLA]
  have hd₀ : Module.finrank (ZMod 2) (moved (ρ.comp N.subtype) (A.subgroupOf N)) ≤ 2 := by
    change Module.finrank (ZMod 2) (subspaceCommutator (ρ.comp N.subtype) ⊤ (A.subgroupOf N)) ≤ 2
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hAN]
    exact hd
  let : IsQuasisimple (L.subgroupOf N) := hLNs.2
  have hi := ChapterB.component_irrPlus_of_minimal_plane (ρ.comp N.subtype)
    (hf.comp N.subtype_injective) hA₀ hcomm hd₀
  obtain ⟨p,hq,he,hm⟩ := ff_component_marked_seed (ρ.comp N.subtype)
    (offenderSubgroup_hypothesis ρ hf hcore cover) hLNs hA₀ hcomm hi
  exact ⟨hLN,hAN,hcomm,p,hq,he,hm⟩
end CFSG.Quasithin.ChapterB.SourceInduction
