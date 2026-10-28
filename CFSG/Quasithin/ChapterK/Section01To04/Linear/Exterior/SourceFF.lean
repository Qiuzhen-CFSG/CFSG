module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Exterior.SourceFF.Offenders
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Exterior.SourceFF.Recognition
public import Theory.Representation.BinaryOffender.EquivariantBest

/-!
# The exterior-square source row of B.4.2

The original action identification forces G=L through the proved full
normalizer. Transport of best offenders gives the actual end-node radicals,
while the model calculation gives the global ratio one. These same
coordinates instantiate every clause of B.4.2(11). The dimension-ten
application obtains its intertwiner from the exhaustive module theorem.

Source: Aschbacher–Smith B.4.2(11) and K.3.2.3, printed pp.86,455.
-/

public section
noncomputable section
open Representation Representation.SL5TenDimensional Representation.BinaryOffender
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterK.Linear.Exterior.SourceFF
open ChapterB.QuasisimpleSource
variable {G V : Type*} [_root_.Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G} {K : GroupClass}

theorem source_of_recognized (h : Recognition.SourceHypothesis K ρ L)
    (e : ActionEquiv (ρ.comp L.subtype) (exteriorAction 2)) :
    L = ⊤ ∧ offenderSubgroup ρ = L ∧ quadraticRatio ρ = 1 ∧
      (∀ A, IsBestOffender ρ A → IsEndNodeRadical ((A.subgroupOf L).map e.groupEquiv.toMonoidHom)) ∧
      ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) := by
  let := h.finite_group
  let := h.finite_module
  have hL := whole_of_exterior h e
  let a := Alternating.wholeAction hL e
  have hq : quadraticRatio ρ = 1 :=
    (Alternating.quadraticRatio_eq a).trans exterior_quadraticRatio
  have hoff (A : Subgroup G) (hA : IsBestOffender ρ A) :
      IsEndNodeRadical ((A.subgroupOf L).map e.groupEquiv.toMonoidHom) := by
    have hAL : A ≤ L := by rw [hL]; exact le_top
    apply best_endNode
    exact (hA.subgroupOf ρ hAL).map_equivariant (ρ.comp L.subtype)
      (exteriorAction 2) e.groupEquiv e.linearEquiv e.intertwines
  have hg : offenderSubgroup ρ = L := by
    let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) :=
      Atlas.psl_simple_high_rank 5 (by decide)
    let : IsSimpleGroup Group := projectiveEquiv.isSimpleGroup
    let : IsSimpleGroup G := a.groupEquiv.isSimpleGroup
    have hff : IsFFModule ρ := (isFFModule_iff_quadraticRatio_le_one ρ).mpr hq.le
    exact ((offenderSubgroup_normal ρ).eq_bot_or_eq_top.resolve_left
      (offenderSubgroup_ne_bot_of_ff ρ hff)).trans hL.symm
  refine ⟨hL, hg, hq, hoff, .exteriorFive hg hL e.groupEquiv ?_ hoff hq⟩
  exact e.linearEquiv.finrank_eq.trans finrank_exteriorModule_two

theorem actionCase_of_finrank (h : Recognition.SourceHypothesis K ρ L)
    (e₀ : L ≃* Group) (hd : Module.finrank (ZMod 2) V = 10) :
    ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) := by
  obtain ⟨e⟩ := exteriorAction_of_finrank h e₀ hd
  exact (source_of_recognized h e).2.2.2.2

end CFSG.Quasithin.ChapterK.Linear.Exterior.SourceFF
