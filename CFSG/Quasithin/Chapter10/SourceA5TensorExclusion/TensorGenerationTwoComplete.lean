module

public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorGenerationOneComplete

/-!
# Generation two for an actual tensor `HStar` member

The tensor generation theorem is stated in terms of a separate
`HasMaximalOutside` witness.  For an actual `HStar` member this witness is
already forced by the nontrivial two-core in the defining `H`-family: choose a
maximal two-local overgroup of the member and compare it with the selected
maximal local subgroup.  This extension discharges that standing guard and
retains the literal `HStar` subgroup in the conclusion.

Source: Aschbacher--Smith 1.1.1 and 9.2.7, together with the standing
post-2.1.1 two-maximal-local hypothesis.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- An actual tensor `HStar` member has generation parameter two.  Its
nontrivial two-core supplies a maximal two-local outside the selected local
subgroup, so the generation-one tensor contradiction applies directly. -/
theorem tensor_hstar_generation_eq_two_of_hstar
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    generationParameter H = 2 := by
  have hcore : pCore 2 H ≠ ⊥ := by
    intro hb
    apply hH.1.1.1
    change (pCore 2 H).map H.subtype = ⊥
    rw [hb, Subgroup.map_bot]
  obtain ⟨M, hM, hHM⟩ :=
    exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot H hcore
  have hout : Chapter3.HasMaximalOutside T D.maximalLocal :=
    Chapter3.hasMaximalOutside_of_two_distinct
      (D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)).1 hM
      (le_normalizer_componentOrbit L T) (hH.1.1.2.trans hHM)
      (fun he => hH.1.2 (he ▸ hHM))
  exact m.tensor_hstar_generation_eq_two hout hH

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
