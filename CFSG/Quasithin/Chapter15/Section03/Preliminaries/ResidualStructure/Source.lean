module
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.SourceOddCenter
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.SourceCyclic
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Source
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl.Pair
public import CFSG.Quasithin.Chapter13.Section09.Source

/-!
# The original orthogonal residual with 14.1.17(3)--(4) discharged

The actual module centralizer lies in Mc because it centralizes the central
involutions. Its commutator with the intersection core gives both star clauses
of 14.1.17(3); quasithinness and the original faithful cyclic action give (4).
The proved orthogonal Sylow geometry supplies the residual/uniqueness dichotomy.
Together these construct every earlier input for the two full 15.3.7 residual
alternatives. The original wreath exclusion also discharges 15.3.9.

The remaining preceding source inputs are the natural action from 15.1.3,
the distinct ordering maximum from 14.1.12 and the actual intersection-core
noncentrality from 14.1.17(1). They are not conclusions replaced by a record.
Source: Aschbacher--Smith, printed pp.980,1121--1123.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03
open ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- All residual inputs except the genuine earlier core noncentrality are derived. -/
theorem residualEarlierInputs_from_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {M Mc : Subgroup G}
    (d : NaturalOrthogonalAction M (localModule T M))
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : Mc ≠ M)
    (hcore : ¬ (M ⊓ Mc).pCoreIn 2 ≤ centralizer (localModule T M : Set G)) :
    ResidualEarlierInputs M Mc (localModule T M) T := by
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hC : M ⊓ centralizer (localModule T M : Set G) ≤ Mc :=
    inf_le_right.trans ((centralizer_le (le_conjugateSpanBy _ _)).trans hMc.2)
  refine {
    sylow_le := hM.1.2
    sylow_le_partner := ?_
    partner_maximal := hMc.1
    partner_ne := hne
    centralizer_le_partner := hC
    module_le := localModule_le T hM.1.2
    overgroup_dichotomy := ?_
    core_noncentral := hcore
    star_centralizes := source_star_centralizes M Mc (localModule T M) d hC
    star_odd_center := source_star_odd_center M Mc (localModule T M) d hC
    faithful_cyclic := fun r hr hn hf P => source_faithful_cyclic hG T hM.1 r hr hn hf P
    rank_bound := (hG.twoLocal_sqtk hM.1.1.1).stronglyQuasithin 3 Nat.prime_three (by decide)
    characteristic_two := hG.evenCharacteristic T M hM.1.1 hM.1.2 }
  · apply le_trans _ hMc.2
    exact le_centralizer_iff.mpr (centralInvolutions_le_centralizer_sylow T)
  · intro X hTX hXM
    rcases source_lemma_15_3_2_4 T d hM hTX hXM with hs | hf
    · exact Or.inl (hs.trans inf_le_right)
    · exact Or.inr hf.2

/-- Both complete source alternatives, on the literal normal-closure residual. -/
theorem source_lemma_15_3_7
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {M Mc : Subgroup G}
    (d : NaturalOrthogonalAction M (localModule T M))
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : Mc ≠ M)
    (hcore : ¬ (M ⊓ Mc).pCoreIn 2 ≤ centralizer (localModule T M : Set G)) :
    ((residualY M Mc).subgroupOf M).map d.actor =
        twoResidualAmbient (⊤ : Subgroup OrthogonalActor) ∧
    M ⊓ Mc = (M ⊓ centralizer (localModule T M : Set G)) ⊔ (T : Subgroup G) ∧
    ((M ⊓ Mc : Subgroup G) : Set G) =
      ((M ⊓ centralizer (localModule T M : Set G) : Subgroup G) : Set G) * (T : Set G) ∧
    M = normalizer (residualY M Mc : Set G) ∧
    Chapter4.UniqueMaximalOvergroup (residualY M Mc ⊔ (T : Subgroup G)) M ∧
    (residualY M Mc ⊔ (T : Subgroup G)).pCoreIn 2 =
      (T : Subgroup G) ⊓ centralizer (localModule T M : Set G) ∧
    (ThreeAlternatives.ElementaryAlternative M Mc (localModule T M) ∨
      ThreeAlternatives.ExtraspecialAlternative M Mc (localModule T M) d) :=
  lemma_15_3_7_from_earlier_source M Mc (localModule T M) T d
    (residualEarlierInputs_from_source hG T d hM hu hne hcore)

/-- Strict two-core containment and the exclusion of the actual A₄ × A₄ residual. -/
theorem source_lemma_15_3_9
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {M Mc : Subgroup G}
    (d : NaturalOrthogonalAction M (localModule T M))
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : Mc ≠ M)
    (hcore : ¬ (M ⊓ Mc).pCoreIn 2 ≤ centralizer (localModule T M : Set G)) :
    localModule T M < (residualY M Mc).pCoreIn 2 ∧
      ¬ Nonempty (residualY M Mc ≃* (alternatingGroup (Fin 4) × alternatingGroup (Fin 4))) := by
  apply lemma_15_3_9_from_earlier_source M Mc (localModule T M) T d
    (residualEarlierInputs_from_source hG T d hM hu hne hcore) rfl
  rintro ⟨e⟩
  exact Chapter13.Section09.false_of_maximal_wreath hG T M hM.1.1 hM.1.2 e

end CFSG.Quasithin.Chapter15.Section03
