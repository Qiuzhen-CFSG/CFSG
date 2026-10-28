module

public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.Domain
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryNatural
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.OrthogonalSix.Assembly
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Covers

/-!
# The complete binary SL₄ and A₈ branches of B.4.2

The odd-center covering theorem recovers the actual original layer from its
A₈ central quotient. The completed cubic sieve gives degree four or the
six-dimensional orthogonal module. Faithfulness recognizes the natural
four-space, while the literal split-form comparison identifies the orthogonal
module with the deleted A₈ module. Its full normalizer retains both A₈ and S₈
ambient actions, with their distinct ratios and offender conclusions.

Source: Aschbacher–Smith K.3.2.1–2, B.4.2(9–10).
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.SourceClassification
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

theorem binary_four_cover (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (e : L ⧸ center L ≃* alternatingGroup (Fin 8)) :
    Nonempty (L ≃* SL(4,ZMod 2)) := by
  let := h.quasisimple
  have ho := ChapterK.Alternating.component_center_odd ρ L h.faithful h.irreducible
  have hz : Nat.card (center L) = 1 := by
    rcases GLS3.Chapter5.OddCentralCovers.odd_center_alternatives 8 (by decide) e ho with h | h
    · exact h
    · omega
  exact ⟨(GLS3.Chapter5.OddCentralCovers.alternatingEquivOfCenterCardOne 8 e hz).trans
    ChapterK.Linear.OrthogonalSix.sl4EquivAlternating.symm⟩
theorem orthogonal_eight_case (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hq : ChapterG.Section09.Quasiequivalent (ρ.comp L.subtype)
      Representation.BinaryLinearRecognition.orthogonalEightAction) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) := by
  let := h.layer_normal
  obtain ⟨e,f,hf⟩ := hq
  let d := Atlas.Order20160A8.DeletedEight.splitEquiv.trans
    ChapterK.Linear.OrthogonalSix.deletedEightEquivNatural
  let a : ActionEquiv (ρ.comp L.subtype) (alternatingNatural 8) := {
    groupEquiv := e
    linearEquiv := f.trans d
    intertwines := by
      intro g v
      change d (f (ρ g v)) = _
      rw [show f (ρ g v) = _ from hf g v]
      change ChapterK.Linear.OrthogonalSix.deletedEightEquivNatural
        (Atlas.Order20160A8.DeletedEight.splitEquiv
          (Atlas.Order20160A8.DeletedEight.splitEquiv.symm
            (Atlas.Order20160A8.DeletedEight.quotientPerm (e g).val
              (Atlas.Order20160A8.DeletedEight.splitEquiv (f v))))) = _
      rw [LinearEquiv.apply_symm_apply]
      exact ChapterK.Linear.OrthogonalSix.deletedEightEquivNatural_intertwines _ _ }
  exact ChapterK.Linear.OrthogonalSix.ambient_case ρ L h.faithful a

/-- Every source binary SL₄ module yields its full corrected action row. -/
theorem binary_four_case (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (e : L ≃* SL(4,ZMod 2)) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) := by
  have hs : ChapterK.Linear.Recognition.SourceHypothesis KnownSimple.IsKnownSimple ρ L :=
    ⟨inferInstance,inferInstance,h.sqtk,h.fitting,h.quasisimple,h.faithful,h.irreducible,h.smallCubic⟩
  rcases ChapterK.Linear.Recognition.BinaryCubicSieve.four_small_modules hs e with hd | ho
  · exact ChapterK.Linear.Recognition.BinaryNatural.actionCase_of_finrank h 4 (Or.inl rfl) e hd
  · exact orthogonal_eight_case h ho

/-- The A₈ quotient branch includes all permitted ambient outer actions. -/
theorem alternating_eight_case (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (e : L ⧸ center L ≃* alternatingGroup (Fin 8)) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) := by
  obtain ⟨j⟩ := binary_four_cover h e
  exact binary_four_case h j

/-- The projective linear presentation of the same source family. -/
theorem binary_four_model_case (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (he : ClassicalGroup.IsPSL (L ⧸ center L) 4 2) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) := by
  obtain ⟨F,_,_,hc,⟨e⟩⟩ := he
  let := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hc)
  exact alternating_eight_case h ((e.trans (Atlas.fieldEquivPSL 4 eF)).trans
    Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8)

/-- Original B.4.2 source hypotheses supply the cubic bound internally. -/
theorem binary_four_of_bestOffender (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (hfit : generalizedFitting G = L) (hL : IsQuasisimple L)
    (hf : Function.Injective ρ) (hi : IsIrreducible (ρ.comp L.subtype))
    {A : Subgroup G} (hA : IsBestOffender ρ A)
    (he : ClassicalGroup.IsPSL (L ⧸ center L) 4 2) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) :=
  binary_four_model_case (source_hypotheses_of_bestOffender hsq hfit hL hf hi hA) he

end CFSG.Quasithin.ChapterB.SourceClassification
