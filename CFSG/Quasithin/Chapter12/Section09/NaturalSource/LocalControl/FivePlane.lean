module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PlaneReduction
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups.ThreeRankOne

/-!
# Complete plane control in original degree five

The actual point quotient is PSL₅(2), and the already proved inner Sylow
action identifies K₁T/O₂(K₁T) with GL₅(2), using the literal quotient map.
The original perfect L₂, defined with the solvable residual, lies in L₁
and the plane normalizer. Hence L₂T ≤ Y. Its nonsolvability survives the
two-group kernel. The proved three-rank bound for Y and the binary flag
lattice force equality Y=L₂T, which supplies the original plane-centralizer
bound and every clause of LocalControl on the same flag and component.

This completes the degree-five local step from an abelian point span.
The degree-four plane argument and nonabelian catalogue construction remain
separate obligations of the natural-branch assembly.

Source: Aschbacher--Smith, 12.9.7, printed p.862 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag
open BinaryLinear.OuterCyclic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- In degree five the original plane join is exactly L₂T. The solvable
residual convention for L₂ is retained. -/
theorem five_planeCentralizerJoin_eq_plane_residual_join
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L) :
    planeCentralizerJoin F C = F.Li L 2 ⊔ (T : Subgroup G) := by
  let X := C.K1 ⊔ (T : Subgroup G)
  let Y := planeCentralizerJoin F C
  let B := F.Li L 2 ⊔ (T : Subgroup G)
  have hLX : F.Li L 2 ≤ X :=
    (Components.five_plane_residual_le_point h F).trans (C.contains.trans le_sup_left)
  have hBY : B ≤ Y := sup_le
    (le_inf hLX (by
      rw [←point_plane_eq_tilde_centralizer h F]
      exact le_inf ((Components.five_plane_residual_le_point h F).trans
        ((F.Li_le L 1).trans inf_le_right)) ((F.Li_le L 2).trans inf_le_right)))
    (planeCentralizerJoin_placements h F C).1
  have hYX : Y ≤ X := inf_le_left
  have hBX : B ≤ X := hBY.trans hYX
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  have hB : ¬ Group.IsSolvable B := by
    intro hs
    let := hs
    exact (Components.Li_mem_local h earlier F 2
      (Or.inl ⟨rfl,by decide,by decide⟩)).1.not_isSolvable inferInstance
  have hm := five_point_model_of_abelian h earlier F hab C
  obtain ⟨k,_,_,hcard,⟨e₀⟩⟩ := hm
  let ek := Theory.SpecificGroups.SymplecticSix.fieldEquivZModTwo k hcard
  let e := (e₀.trans (Atlas.fieldEquivPSL 5 ek)).trans
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 5))
  have hz : center (C.K1 ⧸ pCore 2 C.K1) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    let eS := e.trans (slEquivLinear 5).symm
    have he : eS x ∈ center (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :=
      (centerCongr eS ⟨x,hx⟩).property
    rw [binary_center_eq_bot (by decide),mem_bot] at he
    exact mem_bot.mpr (eS.map_eq_one_iff.mp he)
  let hTN := (F.invariant 1).trans
    ((normal_subgroupOf_iff_le_normalizer C.point_le).mp C.normal)
  have hi := binary_sylow_acts_inner h (Or.inr rfl) earlier F C (Or.inr rfl)
    (show ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 5 2 from
      ⟨k,inferInstance,inferInstance,hcard,⟨e₀⟩⟩)
  let eX := (pCoreJoinQuotientEquivOfInner C.K1 (T : Subgroup G)
    hTN T.isPGroup' hz hi).trans e
  let q := eX.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hq : Function.Surjective q := eX.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 q.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ eX.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hP : ¬ Group.IsSolvable (B.subgroupOf X) := by
    intro hs
    let := hs
    exact hB (Group.isSolvable_of_surjective
      (f := (subgroupOfEquivOfLe hBX).toMonoidHom) (subgroupOfEquivOfLe hBX).surjective)
  have hr : primeRank 3 (Y.subgroupOf X) ≤ 1 := by
    rw [primeRank_equiv 3 (subgroupOfEquivOfLe hYX)]
    exact planeCentralizerJoin_three_rank h (Or.inr rfl) earlier F hab C
  have he := BinaryLinear.SylowFlagOvergroups.five_eq_of_two_kernel_nonsolvable_and_three_rank
    q hq hk (T.subtype hTX) (B.subgroupOf X) (Y.subgroupOf X)
    (comap_mono (show (T : Subgroup G) ≤ B from le_sup_right)) (comap_mono hBY) hP hr
  have hh := congrArg (map X.subtype) he
  rw [map_subgroupOf_eq_of_le hBX,map_subgroupOf_eq_of_le hYX] at hh
  exact hh.symm

/-- The original plane-centralizer bound is unconditional in the abelian
point-span branch of degree five. -/
theorem five_plane_centralizer_le_normalizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L) :
    centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G) := by
  apply plane_centralizer_le_of_join_le_point_parabolic h (Or.inr rfl) earlier F hab C
  rw [five_planeCentralizerJoin_eq_plane_residual_join h earlier F hab C]
  exact sup_le_sup_right (Components.five_plane_residual_le_point h F) _

/-- All original local-control clauses in degree five, on the same flag and
component. No plane bound, model marking, or local-control premise is assumed. -/
theorem five_localControl_of_abelian
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L) :
    LocalControl C := by
  apply localControl_of_abelian_and_plane_join h (Or.inr rfl) earlier F hab C
  rw [five_planeCentralizerJoin_eq_plane_residual_join h earlier F hab C]
  exact sup_le_sup_right (Components.five_plane_residual_le_point h F) _

end CFSG.Quasithin.Chapter12.Section09.NaturalSource
