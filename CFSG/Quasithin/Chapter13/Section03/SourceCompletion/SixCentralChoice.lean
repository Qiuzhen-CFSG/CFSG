module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SixChoice
public import Theory.Alternating.proposition_5_2_7_8
public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow
public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource.Hypothesis1311
/-!
# The original A₆ choice before its module classification

A local component whose quotient by O₂,Z is A₆ has an A₆ section in every
local overgroup. The nonquasisimple radical-quotient theorem would put this
section in prime-field PSL₂(p), which is impossible. Thus its two-core
quotient is quasisimple. Schur's center bound and the trivial two-core give
precisely A₆ or its central three-cover, and the cubic-rank obstruction
proves T-normality.

For a maximal member of the standing counterexample predicate, every larger
local component is faithful. Its A₆ section rules out an A₅ quotient, so it
satisfies the same counterexample predicate and equals the selected component.
This proves the actual Hypothesis 12.2.1 before any natural-module or flag
choice. The final consumer constructs Hypothesis 12.2.3 and a literal Irr⁺
member from the same central quotient, covering both A₆ and the three-cover.
T-invariance and the natural/core classification of that member remain the
separate representation-theoretic part of 13.3.2.

Source: Aschbacher–Smith, 13.3.2(1–4), printed pp.884–885, specialized to
the central quotient in Hypothesis13.7.1, p.935; GLS3, Theorem5.2.3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixCentralChoice
open Chapter1.Section02.LocalModels Chapter12.Section02
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem six_not_solvable : ¬ Group.IsSolvable (alternatingGroup (Fin 6)) := by
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by norm_num)⟩
  exact Group.IsPerfect.not_isSolvable _

/-- The actual A₆ central quotient excludes the nonquasisimple case in
any containing local component, including the original component itself. -/
theorem local_overgroup_quasisimple_of_central_six
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L I : Subgroup G} (hI : I ∈ Chapter1.L G (T : Subgroup G)) (hLI : L ≤ I)
    (e : (L ⧸ centralCore L) ≃* alternatingGroup (Fin 6)) :
    IsQuasisimple (I ⧸ pCore 2 I) := by
  classical
  by_contra hn
  obtain ⟨p, hp, hlarge, F, _, _, hF, ⟨eI⟩⟩ :=
    Chapter13.Section01.nonquasisimple_local_radical_quotient hG T hI hn
  let : Fact p.Prime := ⟨hp⟩
  have ho : Odd p := hp.odd_of_ne_two (by omega)
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let m : Group.SolvableKernelModel I (BenderSuzuki.MatrixGroups.PSL2MatrixGroup F) := {
    kernel := solvableRadical I
    normal := inferInstance
    solvable := inferInstance
    quotientEquiv := eI }
  let f : L.subgroupOf I →* alternatingGroup (Fin 6) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (centralCore L)).comp
      (subgroupOfEquivOfLe hLI).toMonoidHom)
  have hf : Function.Surjective f :=
    e.surjective.comp ((QuotientGroup.mk'_surjective _).comp
      (subgroupOfEquivOfLe hLI).surjective)
  obtain ⟨W, g, hg⟩ := m.simple_section six_not_solvable (L.subgroupOf I) f hf
  exact SixMaximality.prime_psl_no_six_section ho hlarge hF W g hg

/-- Recover both possible two-core quotients from the literal O₂,Z quotient;
no cover-model or normality assumption is needed. -/
theorem local_core_model_of_central_six
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ Chapter1.L G (T : Subgroup G))
    (e : (L ⧸ centralCore L) ≃* alternatingGroup (Fin 6)) :
    IsAlternating (L ⧸ pCore 2 L) 6 ∨ IsAlternatingCover (L ⧸ pCore 2 L) 6 := by
  let Q := L ⧸ pCore 2 L
  let : IsQuasisimple Q := local_overgroup_quasisimple_of_central_six hG T hL le_rfl e
  let eQ : (Q ⧸ center Q) ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.equivOfSurjectiveComap (QuotientGroup.mk' (pCore 2 L))
      (QuotientGroup.mk'_surjective _) (centralCore L) (center Q) rfl).symm.trans e
  have hodd : Odd (Nat.card (center Q)) := by
    apply Nat.not_even_iff_odd.mp
    rw [even_iff_two_dvd]
    exact PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot
      (pCore_quotient_pCore_eq_bot 2) (center Q) le_rfl
  have hd : Nat.card (center Q) ∣ 6 :=
    GLS3.Chapter5.exceptional_alternating_center_card_dvd_six 6 eQ (Or.inl rfl)
  have hd3 : Nat.card (center Q) ∣ 3 := hodd.coprime_two_right.dvd_of_dvd_mul_left
    (by simpa using hd)
  rcases (Nat.dvd_prime Nat.prime_three).mp hd3 with h1 | h3
  · have hz : center Q = ⊥ := Subgroup.card_eq_one.mp h1
    exact Or.inl ⟨QuotientGroup.quotientBot.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hz.symm).trans eQ)⟩
  · let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact Or.inr ⟨inferInstance, ⟨mulEquivOfPrimeCardEq h3 (by simp)⟩, ⟨eQ⟩⟩

private theorem no_five_over_central_six {L I : Subgroup G} (hLI : L ≤ I)
    (e : (L ⧸ centralCore L) ≃* alternatingGroup (Fin 6)) :
    ¬ Nonempty ((I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 5)) := by
  rintro ⟨eI⟩
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsNilpotent (pCore 2 I) := pCore_isPGroup.isNilpotent
  let m : Group.SolvableKernelModel I (alternatingGroup (Fin 5)) := {
    kernel := pCore 2 I
    normal := inferInstance
    solvable := inferInstance
    quotientEquiv := eI }
  let f : L.subgroupOf I →* alternatingGroup (Fin 6) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (centralCore L)).comp
      (subgroupOfEquivOfLe hLI).toMonoidHom)
  have hf : Function.Surjective f :=
    e.surjective.comp ((QuotientGroup.mk'_surjective _).comp
      (subgroupOfEquivOfLe hLI).surjective)
  obtain ⟨W, g, hg⟩ := m.simple_section six_not_solvable (L.subgroupOf I) f hf
  have hd := (Subgroup.card_dvd_of_surjective g hg).trans W.card_subgroup_dvd_card
  have h6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup]
    norm_num
  have h5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup]
    norm_num
  rw [h6, h5] at hd
  norm_num at hd

/-- The selected original A₆ central-quotient branch has the genuine maximal
faithful-local hypothesis, without a natural-module setup. -/
theorem hypothesis1221_of_maximal_central_six
    {T : Sylow 2 G} {L : Subgroup G} (hmax : Maximal (Counterexample T) L)
    (e : (L ⧸ centralCore L) ≃* alternatingGroup (Fin 6)) :
    Hypothesis1221 KnownSimple.IsKnownSimple T L := by
  have d := hmax.1
  have hL := (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T L).mp
    d.local_component
  have hm := local_core_model_of_central_six d.qtke T hL.1 e
  have hTL := local_six_sylow_normalizes d.qtke hL.1 hm
  refine ⟨d.qtke, ⟨⟨hL.1, ?_⟩, hL.2⟩,
    local_overgroup_quasisimple_of_central_six d.qtke T hL.1 le_rfl e⟩
  intro I hI hLI
  have hTI := Chapter1.Section02.Adequate.local_chain_normalizes hL.1 hI hLI hTL
  have hnormalizers : (T : Subgroup G) ⊓ normalizer (L : Set G) =
      (T : Subgroup G) ⊓ normalizer (I : Set G) := by
    rw [inf_of_le_left hTL, inf_of_le_left hTI]
  have hf := (Chapter1.Section02.Adequate.faithful_chain_of_A410_of_normalizer_eq
    T (d.qtke.evenCharacteristic T) ChapterA.Section04.SourceChains.adequate_source
    d.local_component hI hLI hnormalizers).2
  have hcounter : Counterexample T I := {
    d with
    local_component := hf
    five_minimal := fun he => (no_five_over_central_six hLI e he).elim }
  exact le_antisymm (hmax.2 hcounter hLI) hLI

/-- The actual consumer: construct the earlier source hypotheses and choose
a module in the original R₂(LT), before classifying its representation. -/
theorem chosen_setup_of_maximal_central_six
    {T : Sylow 2 G} {L : Subgroup G} (hmax : Maximal (Counterexample T) L)
    (e : (L ⧸ centralCore L) ≃* alternatingGroup (Fin 6)) :
    Hypothesis1223 KnownSimple.IsKnownSimple T L ∧
      (T : Subgroup G) ≤ normalizer (L : Set G) ∧
      ∃ V : Subgroup G, Nonempty (ChosenModule T L V) := by
  have h := hypothesis1221_of_maximal_central_six hmax e
  have hL := (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T L).mp
    hmax.1.local_component
  exact ⟨(Chapter14.Section03.FaithfulSource.Counterexample.hypothesis1311 hmax.1).hypothesis1223
    h.maximal_faithful h.quasisimple,
    faithful_local_six_exists_chosen hmax.1.qtke hmax.1.local_component
      (local_core_model_of_central_six hmax.1.qtke T hL.1 e)⟩
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixCentralChoice
