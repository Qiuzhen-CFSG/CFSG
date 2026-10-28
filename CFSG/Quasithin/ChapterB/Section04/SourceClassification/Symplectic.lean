module

public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.Domain
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract

/-!
# The full even symplectic four-space branch of B.4.2

The proved K.3.4 recognition yields the natural module or the descended
tensor. Its strict quadratic bound excludes the tensor for an FF-module.
The remaining actual intertwiner, ratio and offender generation give the
literal corrected B.4.2(3) row. The public model theorem starts with the
projective central quotient and constructs the binary field and its marking.

Source: Aschbacher--Smith B.4.2(3), K.3.4, pp.86 and 456--457.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterB.SourceClassification
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

theorem symplectic_case (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hff : IsFFModule ρ) (F : BinaryField) (hF : 1 < F.degree)
    (e : L ⧸ center L ≃* Theory.SpecificGroups.SymplecticFour.Sp F.Carrier) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) := by
  have hs : ChapterK.Symplectic.SourceHypothesis KnownSimple.IsKnownSimple ρ L := {
    finite_group := inferInstance
    finite_module := inferInstance
    sqtk := h.sqtk
    fitting := h.fitting
    quasisimple := h.quasisimple
    faithful := h.faithful
    irreducible := h.irreducible
    cubic_le_two := h.smallCubic }
  let := h.irreducible
  obtain ⟨_,_,_,hnat | hten⟩ := ChapterK.Symplectic.source_complete hs hF F.card_eq e
  · obtain ⟨M,_,hr,hgen,_⟩ := hnat
    let a : ActionEquiv (ρ.comp L.subtype) (binarySymplectic F) := {
      groupEquiv := M.groupEquiv
      linearEquiv := M.linearEquiv
      intertwines := M.intertwines }
    exact .symplectic F hF hgen a hr
  · obtain ⟨s,_,_,a,M,hgeom⟩ := hten
    have hq := (isFFModule_iff_quadraticRatio_le_one ρ).mp hff
    have hb := hgeom.2.1
    exact (not_lt_of_ge (hq.trans (by norm_num : (1 : ENNReal) ≤ 2)) hb).elim

theorem symplectic_model_case (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hff : IsFFModule ρ) {r : ℕ} (hr : 2 ≤ r)
    (he : ClassicalGroup.IsPSp (L ⧸ center L) 2 (2 ^ r)) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) := by
  obtain ⟨F,_,_,hcard,⟨e⟩⟩ := he
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let K : BinaryField := {
    Carrier := F
    degree := r
    degree_pos := by omega
    card_eq := hcard }
  exact symplectic_case h hff K (by change 1 < r; omega)
    (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm)

/-- Apply this source family to the original B.4.2 hypotheses and best offender. -/
theorem symplectic_of_bestOffender (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (hfit : generalizedFitting G = L) (hL : IsQuasisimple L)
    (hf : Function.Injective ρ) (hi : IsIrreducible (ρ.comp L.subtype))
    {A : Subgroup G} (hA : IsBestOffender ρ A)
    {r : ℕ} (hr : 2 ≤ r) (he : ClassicalGroup.IsPSp (L ⧸ center L) 2 (2 ^ r)) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) :=
  symplectic_model_case (source_hypotheses_of_bestOffender hsq hfit hL hf hi hA)
    ⟨A,hA.isOffender ρ⟩ hr he
end CFSG.Quasithin.ChapterB.SourceClassification
