module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.SourceAction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.SixModels
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.AlternatingSixMovedCover.Full
/-!
# The original A₆ moved subgroup and its possible central cover

The natural central quotient of the original U_K has dimension four.
Its universal augmentation cover has dimension five. Consequently the
literal U_K has order sixteen or thirty-two. In the latter case the
universal cover is the full module, retaining its central fixed line.
These statements require neither a short group nor a block.

Source: Aschbacher--Smith B.5.1 and the source selection in 13.6.22, p.932.
The whole-core identification [O₂(K),K]=U_K remains separate.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly
open ChapterB.QuasisimpleSource ComponentSelection SourceContainment SourceContainment.LinearThree.CentralAction.ModuleAlternatives
variable {G : Type*} [Group G] [Finite G]
variable (K L T : Subgroup G) (z v : G)
variable (hL : Tv T v ≤ normalizer (Lv L v : Set G))
variable (hz : Tv T v ≤ centralizer ({z} : Set G))
variable [IsElementaryAbelian 2 (WK K L T z v)]
variable [(plusImage K L T z v hL hz K).Normal]

theorem six_moved_card
    (hCJ : plusImage K L T z v hL hz K ≤ offenderSubgroup (wkRepresentation K L T z v hL hz))
    (s : MovedSection ((wkRepresentation K L T z v hL hz).comp
      (offenderSubgroup (wkRepresentation K L T z v hL hz)).subtype)
      ((plusImage K L T z v hL hz K).subgroupOf
        (offenderSubgroup (wkRepresentation K L T z v hL hz))))
    (hi : IsIrrPlus ((wkRepresentation K L T z v hL hz).comp
      (offenderSubgroup (wkRepresentation K L T z v hL hz)).subtype)
      ((plusImage K L T z v hL hz K).subgroupOf
        (offenderSubgroup (wkRepresentation K L T z v hL hz))) s.space.toSubmodule)
    (e : ActionEquiv (s.action.comp
      ((plusImage K L T z v hL hz K).subgroupOf
        (offenderSubgroup (wkRepresentation K L T z v hL hz))).subtype)
        (alternatingNatural 6)) :
    Nat.card (UK K L T z v) = 16 ∨ Nat.card (UK K L T z v) = 32 := by
  let t := Classifier.liftSection hCJ s
  have hcard : Nat.card (UK K L T z v) = Nat.card s.space.toSubmodule := by
    change Nat.card (UK K L T z v) = Nat.card t.space.toSubmodule
    exact (Nat.card_congr (movedEquivUK K L T z v hL hz t).symm.toEquiv).trans
      (Nat.card_congr Multiplicative.toAdd)
  have hu := s.alternatingSix_finrank_le_five hi e
  have hl := s.central.toSubmodule.finrank_quotient_le
  have he := e.linearEquiv.finrank_eq
  rw [BinaryPermutation.finrank_natural_even (Fin 6) (by decide)] at he
  norm_num only [Fintype.card_fin] at he
  rw [he] at hl
  have hn : Module.finrank (ZMod 2) s.space.toSubmodule = 4 ∨
      Module.finrank (ZMod 2) s.space.toSubmodule = 5 := by omega
  rw [hcard,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  rcases hn with hn | hn <;> simp [hn]
/-- In the order-thirty-two branch, the full original moved module is the
six-letter augmentation core, with its actual action and quotient retained. -/
theorem six_augmentation_model_of_actionData
    (m : SixModels.ActionData (wkRepresentation K L T z v hL hz)
      (plusImage K L T z v hL hz K))
    (hc : Nat.card (UK K L T z v) = 32) :
    ∃ e : ActionEquiv (m.conclusion.sectionData.action.comp
      ((plusImage K L T z v hL hz K).subgroupOf
        (offenderSubgroup (wkRepresentation K L T z v hL hz))).subtype)
        (alternatingNatural 6),
    ∃ f : BinaryPermutation.core (Fin 6) ≃ₗ[ZMod 2] m.conclusion.sectionData.space.toSubmodule,
      (∀ g : alternatingGroup (Fin 6), ∀ v,
        f (BinaryPermutation.coreRepresentation (Fin 6) g.val v) =
          m.conclusion.sectionData.space.toRepresentation (e.groupEquiv.symm g) (f v)) ∧
      ∀ v, e.linearEquiv (m.conclusion.sectionData.central.toSubmodule.mkQ (f v)) =
        BinaryPermutation.coreToNatural (Fin 6) v := by
  obtain ⟨e⟩ := m.natural
  let s := m.conclusion.sectionData
  let t := Classifier.liftSection m.component_le_offenders s
  have hcard : Nat.card s.space.toSubmodule = 32 := by
    have h : Nat.card (UK K L T z v) = Nat.card s.space.toSubmodule := by
      change Nat.card (UK K L T z v) = Nat.card t.space.toSubmodule
      exact (Nat.card_congr (movedEquivUK K L T z v hL hz t).symm.toEquiv).trans
        (Nat.card_congr Multiplicative.toAdd)
    exact h.symm.trans hc
  exact ⟨e,s.alternatingSix_core_equiv_of_card m.irrPlus e hcard⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly
