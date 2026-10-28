module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.OriginalNormalizationSource
public import CFSG.Quasithin.ChapterA.Section04.ReducedWitness.Intrinsic
public import Theory.GroupTheory.MaximalTwoLocalTransport

/-!
# Normalization at every Sylow from one original A₅ context

Ambient Sylow conjugacy carries each faithful local component to the family
at the original Sylow. Its intrinsic module remains nontrivial, and the
original uniform A₅ hypothesis marks its literal two-core quotient. The
quotient equivalence transports that mark back to the same component.

The proved original pair normalization then applies at every Sylow. The
multiple-overgroup guard transports by conjugacy and supplies an actual
chosen module there. No module classification or Context transport is used.
Source: Aschbacher--Smith 13.3.1(4),13.3.2(1), printed pp.884--885.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open Section05.A5Source Section03.A5Setup.OriginalMaximality
open Chapter1.Section02.Adequate ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)

include d

/-- The original uniform A₅ clause holds on the faithful local family at
every ambient Sylow, with each component's actual two-core retained. -/
theorem original_faithful_A5_at_every_sylow
    (S : Sylow 2 G) (I : Subgroup G)
    (hI : I ∈ MainForward.faithfulLocalComponents S) :
    Nonempty ((I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G S T
  let e := MulAut.conj g
  have hST : (S : Subgroup G).map e.toMonoidHom = (T : Subgroup G) :=
    congrArg Sylow.toSubgroup hg
  have hIL := (mem_faithfulLocalComponents_iff S I).mp hI
  have hmap : I.map e.toMonoidHom ∈ Chapter1.L G (T : Subgroup G) := by
    rw [←hST]
    exact (Chapter1.mem_L_map_iff e.toMonoidHom e.injective).mpr hIL.1
  have hfaithful : I.map e.toMonoidHom ∈ MainForward.faithfulLocalComponents T := by
    apply (mem_faithfulLocalComponents_iff_module T
      (d.hypothesis.qtke.evenCharacteristic T)).mpr
    refine ⟨hmap,?_⟩
    rw [intrinsicSignalizerModule_map_of_injective e.toMonoidHom e.injective]
    exact fun hz => hIL.2.2
      (((intrinsicSignalizerModule I).map_eq_bot_iff_of_injective e.injective).mp hz)
  obtain ⟨a⟩ := d.uniform_A5 _ hfaithful
  let c := I.equivMapOfInjective e.toMonoidHom e.injective
  let q := QuotientGroup.congr (pCore 2 I) (pCore 2 (I.map e.toMonoidHom)) c
    (pCore_map_iso 2 c)
  exact ⟨q.trans a⟩

/-- Original normalization and actual chosen-module existence at an
arbitrary Sylow, from the same original multiple-overgroup hypothesis. -/
theorem original_normalization_and_chosen_at_every_sylow
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (S : Sylow 2 G) (I : Subgroup G)
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 S I) :
    (S : Subgroup G) ≤ normalizer (I : Set G) ∧
      ∃ W : Subgroup G, Nonempty (Chapter12.Section02.ChosenModule S I W) := by
  obtain ⟨a⟩ := original_faithful_A5_at_every_sylow d S I h.local_component
  apply original_a5_normalizes_from_source_of_many h a
  rwa [maximalTwoLocalOvergroups_ncard_sylow S T]

/-- The universal original normalization input follows from one original
Context; no universal normalization or module-classification premise remains. -/
theorem original_normalization_at_every_sylow
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G) := by
  intro S I h
  exact (original_normalization_and_chosen_at_every_sylow d hmany S I h).1

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
