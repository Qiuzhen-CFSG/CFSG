module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.Context
public import CFSG.Quasithin.Chapter13.Section05.A5Source.Centralizers
public import Theory.GroupTheory.PResidual.PerfectLift
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import CFSG.Quasithin.Chapter1.Section01Overgroups
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Intrinsic local structure from the original A₅ context

Faithful local membership gives two-perfectness and characteristic two.
The actual marked A₅ action has two-core kernel, so perfection lifts to L.
The same kernel is the literal ambient intersection L ∩ C_G(V).
An overgroup of T centralizing the source line has nontrivial two-core;
even characteristic therefore makes it a characteristic-two group.

These facts discharge the local structure inputs in the original F.9.1
application without a classification or a kernel conclusion as an assumption.
Source: Aschbacher–Smith 13.3.1–2, 13.5.7 and 1.1.4(6).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
namespace Context
variable (d : Context T L V V₁ V₂ V₃)
include d

theorem twoPerfect : IsPPerfect 2 L := d.hypothesis.local_component.2.1.2.1

theorem residual_eq_top : pResidual 2 L = ⊤ :=
  (pResidual_eq_top_iff 2 L).mpr d.twoPerfect

theorem characteristic_L : generalizedFitting L = pCore 2 L :=
  d.hypothesis.local_component.2.1.2.2

/-- Perfection comes from the actual A₅ action and its two-core kernel. -/
theorem perfect : Group.IsPerfect L := by
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  apply d.twoPerfect.isPerfect_of_surjective_pGroup_kernel d.flag.module.action d.flag.module.onto
  rw [d.flag.action_kernel]
  exact pCore_isPGroup

/-- The marked action kernel is the genuine centralizer, in the original G. -/
theorem centralizer_eq_core : L ⊓ centralizer (V : Set G) = L.pCoreIn 2 := by
  apply le_antisymm
  · intro l hl
    have ha : d.flag.module.action ⟨l,hl.1⟩ = 1 := by
      apply Subtype.ext
      rw [← d.flag.action_agrees ⟨l,hl.1⟩ (d.flag.module.normalizes hl.1)]
      exact (actor_eq_one_iff d.flag ⟨l,d.flag.module.normalizes hl.1⟩).mpr hl.2
    have hk : (⟨l,hl.1⟩ : L) ∈ pCore 2 L := d.flag.action_kernel ▸ ha
    exact mem_map_of_mem L.subtype hk
  · rintro _ ⟨l,hl,rfl⟩
    refine ⟨l.property,(actor_eq_one_iff d.flag ⟨l,d.flag.module.normalizes l.property⟩).mp ?_⟩
    rw [d.flag.action_agrees]
    have hk : l ∈ d.flag.module.action.ker := d.flag.action_kernel.symm ▸ hl
    have ha : d.flag.module.action l = 1 := hk
    exact congrArg Subtype.val ha

/-- Every original H over T centralizing the source line is of
characteristic two, by the ambient even-characteristic hypothesis. -/
theorem characteristic_H (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hHZ : H ≤ centralizer (V₁ : Set G)) :
    generalizedFitting H = pCore 2 H := by
  have hZT : V₁ ≤ (T : Subgroup G) :=
    d.flag.one_le_two.trans (d.flag.two_le_V.trans d.chosen.le_sylow)
  have hcore : V₁ ≤ H.pCoreIn 2 := le_pCoreIn_of_normalizes
    (T.isPGroup'.to_le hZT) (hZT.trans hTH)
    (hHZ.trans (Subgroup.centralizer_le_normalizer _))
  have hne : H.pCoreIn 2 ≠ ⊥ := by
    intro he
    have hz : V₁ = ⊥ := bot_unique (hcore.trans_eq he)
    have hc := d.flag.one_card
    simp [hz] at hc
  exact generalizedFitting_eq_pCore_of_selfCentralizing 2
    (Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T
      (d.hypothesis.qtke.evenCharacteristic T) ⟨hne,hTH⟩))
end Context
end CFSG.Quasithin.Chapter13.Section05.A5Source

