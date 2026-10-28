module
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.SourceCounterexample
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SixChoice
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental
public import CFSG.Quasithin.Chapter14.Section03.CaseOneSource

/-!
# The ordinary A₆ source choice before module classification

The genuine A₆ quotient makes the local component T-invariant by the
cubic-rank obstruction. Every containing local component is faithful and
has quasisimple two-core quotient. Its quotient cannot be A₅, since that
would exhibit an A₆ section of a group of order sixty. Consequently a
maximal standing counterexample is maximal in the full local family.

This constructs Hypothesis 12.2.3 and a literal Irr⁺ choice before assuming
any natural-module marking, invariant flag, or abelian closure. The actual
Fundamental Setup consumer preserves the same T and L and lets the earlier
module classification act without first constructing its own conclusion.
Source: Aschbacher--Smith 13.3.2(1--4), printed pp.884--885, and the maximal
choice in Theorem D, pp.1078--1079; A.3.8(3) and A.4.11 supply normalization
and the nonzero reduced module.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section03.SourceCompletion.SixMaximality
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

private theorem no_five_over_six_source {L I : Subgroup G} (hLI : L ≤ I)
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

/-- The actual A₆ quotient makes the maximal standing choice maximal in
all local components, before choosing its module or invariant flag. -/
theorem hypothesis1221_of_maximal_six
    (hmax : Maximal (Counterexample T) L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L := by
  have h := hmax.1
  have hL := (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T L).mp h.local_component
  have hn := Chapter12.Section02.local_six_sylow_normalizes h.qtke hL.1 (.inl ⟨e⟩)
  refine ⟨h.qtke, ⟨⟨hL.1, ?_⟩, hL.2⟩,
    local_overgroup_quasisimple_of_six h.qtke T hL.1 le_rfl e⟩
  intro I hI hLI
  have hTI := Chapter1.Section02.Adequate.local_chain_normalizes hL.1 hI hLI hn
  have heq : (T : Subgroup G) ⊓ normalizer (L : Set G) =
      (T : Subgroup G) ⊓ normalizer (I : Set G) := by
    rw [inf_of_le_left hn, inf_of_le_left hTI]
  have hf := (Chapter1.Section02.Adequate.faithful_chain_of_A410_of_normalizer_eq
    T (h.qtke.evenCharacteristic T) ChapterA.Section04.SourceChains.adequate_source
      h.local_component hI hLI heq).2
  have hc : Counterexample T I := {
    h with
    local_component := hf
    five_minimal := fun he => (no_five_over_six_source hLI e he).elim }
  exact le_antisymm (hmax.2 hc hLI) hLI

/-- The full earlier Chapter12 source hypothesis is available before module
classification, using the same selected ordinary A₆ subgroup. -/
theorem hypothesis1223_of_maximal_six
    (hmax : Maximal (Counterexample T) L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L := by
  have h := hypothesis1221_of_maximal_six hmax e
  exact Section03.CaseOneSource.hypothesis1223 hmax.1 h.maximal_faithful h.quasisimple

/-- The original source obtains both 12.2.3 and a genuine Irr⁺ member,
without first supplying a NaturalSetup or a module model. -/
theorem original_six_chosen_source
    (hmax : Maximal (Counterexample T) L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L ∧
      (T : Subgroup G) ≤ normalizer (L : Set G) ∧
      ∃ V : Subgroup G, Nonempty (Chapter12.Section02.ChosenModule T L V) := by
  exact ⟨hypothesis1223_of_maximal_six hmax e,
    Chapter12.Section02.faithful_local_six_exists_chosen hmax.1.qtke
      hmax.1.local_component (.inl ⟨e⟩)⟩

/-- The earlier source classification acts on an actual FundamentalSetup
of this same maximal A₆ subgroup; no natural-module conclusion is needed. -/
theorem exists_original_six_fundamentalSetup
    (hmax : Maximal (Counterexample T) L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    Nonempty (Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L) := by
  obtain ⟨_, _, V, ⟨D⟩⟩ := original_six_chosen_source hmax e
  exact ⟨D.fundamentalSetup (hypothesis1221_of_maximal_six hmax e)⟩

end CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
