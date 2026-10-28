module

public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.Domain
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract

/-!
# The symplectic source branch at quadratic ratio two

The complete K.3.4 recognition supplies a natural action or the descended
symplectic tensor. The latter has quadratic ratio strictly greater than two,
so the original bound leaves the actual natural action and every corresponding
B.4.2 clause. This is the literal symplectic family application of B.4.5 in
13.5.21; no representation recognition premise is added.

Source: Aschbacher–Smith B.4.5 and K.3.4, printed pp.87 and 456–457.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterB.SmallRatioClassification
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

theorem symplectic_case (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hq : quadraticRatio ρ ≤ 2) (F : BinaryField) (hF : 1 < F.degree)
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
    have hb := hgeom.2.1
    exact (not_lt_of_ge hq hb).elim

theorem symplectic_model_case (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hq : quadraticRatio ρ ≤ 2) {r : ℕ} (hr : 2 ≤ r)
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
  exact symplectic_case h hq K (by change 1 < r; omega)
    (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm)

end CFSG.Quasithin.ChapterB.SmallRatioClassification
