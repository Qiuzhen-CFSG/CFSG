module

public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NonblockInitialCenter
public import CFSG.Quasithin.ChapterA.Section04.Modules

/-!
# Intrinsic faithfulness of the actual constrained containing component

The original full module W lies in the moved omega-center of O₂(KS).
The A.4.8 comparison puts this moved layer inside the intrinsic module of K,
so the actual containing component is intrinsically faithful. This uses the
constrained source configuration and no quotient-row or MS classification.

The source intersection S = T ∩ H is smaller than T; intrinsic faithfulness
alone does not supply locality at a full ambient Sylow.

Source: Aschbacher--Smith A.4.8, pp.59--60, and the original containing
configuration 4.3.8--10, pp.616--617.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open ChapterA.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

private theorem component_twoPerfect (c : SourceConfiguration T L) :
    IsPPerfect 2 (K c) := by
  let := c.component.perfect
  let : Group.IsPerfect (K c) := Group.IsPerfect.map c.H.subtype
  intro N hn hp
  let := hn
  let := hp.isNilpotent
  exact top_unique (le_of_isPerfect_of_solvable_quotient ⊤ N)

private theorem initial_le_intrinsicModule (c : SourceConfiguration T L) :
    movedCoreOmega c ≤ intrinsicSignalizerModule (K c) := by
  have hn : K c ⊔ S c ≤ normalizer (K c : Set G) :=
    (sup_le (map_subtype_le _) inf_le_right).trans c.normalizer_component.le
  have hcore : (K c).pCoreIn 2 ≤ (K c ⊔ S c).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left hn
  have hnorm : K c ≤ normalizer ((K c ⊔ S c).pCoreIn 2 : Set G) :=
    (le_sup_left : K c ≤ K c ⊔ S c).trans
      ((K c ⊔ S c).le_normalizer.trans
        (normalizer_le_normalizer_intrinsicCore (K c ⊔ S c)))
  have hcomm : ⁅K c,(K c ⊔ S c).pCoreIn 2⁆ ≤ (K c).pCoreIn 2 := by
    rw [commutator_comm,sylow_join_commutator_eq]
    exact le_normalizer_iff_commutator_le_left.mp
      ((K c).le_normalizer.trans (normalizer_le_normalizer_intrinsicCore (K c)))
  have h := signalizerModule_le_intrinsicModule (K c) ((K c ⊔ S c).pCoreIn 2)
    (component_twoPerfect c) hnorm hcore hcomm
  have he : coreOmega c = Stellmacher.omegaOneCenterAmbient ((K c ⊔ S c).pCoreIn 2) := by
    ext x
    rw [mem_omegaCenterIn_iff,Stellmacher.mem_omegaOneCenterAmbient_iff]
    tauto
  change ⁅coreOmega c,K c⁆ ≤ intrinsicSignalizerModule (K c)
  rw [he]
  simpa only [signalizerModule_eq_commutator_omegaCenter,commutator_comm (K c)] using h

/-- The literal source full module lies in the containing component's intrinsic module. -/
theorem fullModule_le_intrinsicModule (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) :
    W c ≤ intrinsicSignalizerModule (K c) :=
  (InitialCenter.fullModule_le_initial hf).trans (initial_le_intrinsicModule c)

/-- The actual constrained containing component has a nonzero intrinsic module. -/
private theorem component_intrinsicModule_ne_bot (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) :
    intrinsicSignalizerModule (K c) ≠ ⊥ := by
  intro hz
  exact c.c28.module_nontrivial
    (bot_unique ((fullModule_le_intrinsicModule c hf).trans hz.le))

/-- Intrinsic faithfulness retains the original component embedded through H. -/
theorem component_isFaithfulSignalizerType (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) :
    IsFaithfulSignalizerType (K c) := by
  refine ⟨⟨?_,component_twoPerfect c,?_⟩,component_intrinsicModule_ne_bot c hf⟩
  · exact fun hz => c.component.ne_bot
      ((map_eq_bot_iff_of_injective _ c.H.subtype_injective).mp hz)
  · let e : c.K ≃* K c := c.K.equivMapOfInjective c.H.subtype c.H.subtype_injective
    have h := congrArg (fun X : Subgroup c.K => X.map e.toMonoidHom) hf
    simpa only [map_generalizedFitting_equiv,pCore_map_iso] using h

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
