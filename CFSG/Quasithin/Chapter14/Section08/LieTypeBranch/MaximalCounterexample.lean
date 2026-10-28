module

public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.SourceCounterexample
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality

/-!
# Maximal choice for the ordinary A₆ branch of Theorem D

Choose a maximal member of the existing standing counterexample predicate.
This preserves the original uniform A₅ condition. In the natural A₆ branch,
every larger local component is faithful by the proved chain theorem. Its
two-core quotient cannot be A₅: removing the solvable kernel would exhibit
an A₆ section of a group of order sixty. The larger subgroup therefore
satisfies the same standing predicate, and maximal choice makes it equal
to the selected subgroup. This gives the literal Hypothesis 12.2.1 needed
by the ordinary F.9 consumer without the general 13.3.2 maximality theorem.

Source: Aschbacher--Smith, opening choice of Theorem D and Hypotheses 13.3.1,
13.7.1; maximality application in 13.3.2 and the ordinary 13.5 argument.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section08.SourceCompletion
open Chapter13.Section03.SourceCompletion.SixMaximality

universe u
variable {G : Type u} [Group G] [Finite G]

/-- A counterexample to D admits a maximal standing local choice. -/
theorem exists_maximal_counterexample_of_not_theoremDModel
    (h : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hne : (MainForward.faithfulLocalComponents T).Nonempty)
    (hnot : ¬ ClassificationModels.IsTheoremDModel G) :
    ∃ L : Subgroup G, Maximal (Counterexample T) L := by
  obtain ⟨L, hL⟩ := exists_counterexample_of_not_theoremDModel h T hne hnot
  obtain ⟨I, _, hI⟩ := Finite.exists_le_maximal hL
  exact ⟨I, hI⟩

private theorem no_five_over_six {L I : Subgroup G} (hLI : L ≤ I)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    ¬ Nonempty ((I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 5)) := by
  rintro ⟨eI⟩
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by norm_num)⟩
  let : Group.IsNilpotent (pCore 2 I) := pCore_isPGroup.isNilpotent
  let m : Group.SolvableKernelModel I (alternatingGroup (Fin 5)) := {
    kernel := pCore 2 I
    normal := inferInstance
    solvable := inferInstance
    quotientEquiv := eI }
  let f : L.subgroupOf I →* alternatingGroup (Fin 6) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 L)).comp
      (subgroupOfEquivOfLe hLI).toMonoidHom)
  have hf : Function.Surjective f :=
    e.surjective.comp ((QuotientGroup.mk'_surjective _).comp
      (subgroupOfEquivOfLe hLI).surjective)
  obtain ⟨W, g, hg⟩ := m.simple_section (Group.IsPerfect.not_isSolvable _)
    (L.subgroupOf I) f hf
  have hd := (Subgroup.card_dvd_of_surjective g hg).trans W.card_subgroup_dvd_card
  have h6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup]
    norm_num
  have h5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup]
    norm_num
  rw [h6, h5] at hd
  norm_num at hd

/-- The selected natural A₆ component has the exact maximality and quotient
hypotheses required by the original ordinary F.9 construction. -/
theorem hypothesis1221_of_maximal_natural_six
    {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hmax : Maximal (Counterexample T) L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L := by
  have hL := (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T L).mp
    d.counterexample.local_component
  refine ⟨d.counterexample.qtke, ⟨⟨hL.1, ?_⟩, hL.2⟩,
    local_overgroup_quasisimple_of_six d.counterexample.qtke T hL.1 le_rfl e⟩
  intro I hI hLI
  have hTI := Chapter1.Section02.Adequate.local_chain_normalizes
    hL.1 hI hLI d.normalizes_L
  have hnormalizers : (T : Subgroup G) ⊓ normalizer (L : Set G) =
      (T : Subgroup G) ⊓ normalizer (I : Set G) := by
    rw [inf_of_le_left d.normalizes_L, inf_of_le_left hTI]
  have hf := (Chapter1.Section02.Adequate.faithful_chain_of_A410_of_normalizer_eq
    T (d.counterexample.qtke.evenCharacteristic T)
    ChapterA.Section04.SourceChains.adequate_source d.counterexample.local_component
    hI hLI hnormalizers).2
  have hcounter : Counterexample T I := {
    d.counterexample with
    local_component := hf
    five_minimal := fun he => (no_five_over_six hLI e he).elim }
  exact le_antisymm (hmax.2 hcounter hLI) hLI

end CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
