module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Parabolic.SolvablePair
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.MiddleExchange

/-!
# Exclusion of the original rank-ten constrained orbit

The literal component point node and its exchange conjugate have solvable
join. The third, escaping node is fixed by the source exchange. Conjugation
therefore identifies their two joins with that node. In rank ten the plane
centralizer has two-core quotient S₃ × PSL₃(2), of order 1008; its actual
SL₅(2) action and two-group kernel identify it with a middle parabolic.
The concrete flag theorem says that exactly one of those two joins is
solvable, a contradiction. Thus the original orbit has rank five.

This removes the rank-ten branch of LinearFiveExclusionAt without an extra
model or exchange premise. The rank-five contradiction and construction of
LinearFiveData remain with qt-d-10-nona5-point-constrained. In the remaining
printed paragraph, O²(P) denotes the two-residual, not the two-core O₂(P).

Source: Aschbacher--Smith, 10.2.9, printed p.753.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

omit [Finite G] in
private theorem solvable_subgroupOf_iff (A H : Subgroup G) (hAH : A ≤ H) :
    Group.IsSolvable (A.subgroupOf H) ↔ Group.IsSolvable A := by
  let e := subgroupOfEquivOfLe hAH
  constructor
  · intro hs
    let := hs
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  · intro hs
    let := hs
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

/-- The source rank-ten plane centralizer has two-core quotient of order 1008. -/
theorem LinearFiveData.plane_quotient_card_ten {c : Context D t v I}
    (m : LinearFiveData c)
    (hd : letI := c.reduced.elementary
      Module.finrank (ZMod 2) (Additive (internalModule D v I)) = 10) :
    Nat.card (planeCentralizer T t v I ⧸ pCore 2 (planeCentralizer T t v I)) = 1008 := by
  obtain ⟨_,⟨e⟩⟩ := m.plane_structure_ten hd
  rw [Nat.card_congr e.toEquiv,Nat.card_prod]
  have hc : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
    rw [←Nat.card_congr BinaryLinear.SmallParabolicLevi.linearThreeEquivProjective.toEquiv,
      ←Nat.card_congr (BinaryLinear.OuterCyclic.slEquivLinear 3).toEquiv]
    exact BinaryLinear.NaturalThreePoint.group_card
  rw [hc,Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
  decide

/-- The rank-ten branch of the actual constrained linear-five configuration
is impossible. The original exchange identifies joins of different solvability. -/
theorem LinearFiveData.not_dimension_ten {c : Context D t v I}
    (m : LinearFiveData c)
    (hd : letI := c.reduced.elementary
      Module.finrank (ZMod 2) (Additive (internalModule D v I)) = 10) : False := by
  let H := pointJoin T v I
  let C := planeCentralizer T t v I
  let A := componentPointNode T L t v
  let f := (MulAut.conj t).toMonoidHom
  let B := A.map f
  let node : BinaryLinear.FiveFlagGeometry.RankOneBelow (pointSylow T v) C :=
    ⟨A,m.componentPointNode_covBy,m.componentPointNode_le_plane⟩
  have hAB : A ≠ B := m.componentPointNode_moved.symm
  have hBM : B ≤ D.maximalLocal :=
    (m.rankOneExchange_le_maximalLocal_iff node).mpr m.componentPointNode_le_maximalLocal
  obtain ⟨P,hP,hPC,hPM,htP,_⟩ :=
    m.exists_exchange_fixed_escaping_rankOne_of_moved_node node
      m.componentPointNode_le_maximalLocal (fun h => m.componentPointNode_moved (congrArg Subtype.val h))
  have hAP : A ≠ P := fun he => hPM (he ▸ m.componentPointNode_le_maximalLocal)
  have hBP : B ≠ P := fun he => hPM (he ▸ hBM)
  have hBC : B ≤ C := (m.rankOneExchange node).property.2
  have hB : pointSylow T v ⋖ B := (m.rankOneExchange node).property.1
  have hAH : A ≤ H := m.componentPointNode_le_plane.trans inf_le_left
  have hBH : B ≤ H := hBC.trans inf_le_left
  have hPH : P ≤ H := hPC.trans inf_le_left
  have heP : P.map f = P := mem_normalizer_iff_map_conj_eq.mp htP
  let : Group.IsSolvable f.ker := by
    rw [(MonoidHom.ker_eq_bot_iff f).mpr (MulAut.conj t).injective]
    infer_instance
  have hex : Group.IsSolvable (A ⊔ P : Subgroup G) ↔
      Group.IsSolvable (B ⊔ P : Subgroup G) := by
    have he : (A ⊔ P).map f = B ⊔ P := by rw [Subgroup.map_sup,heP]
    rw [←he]
    exact (Group.isSolvable_map_iff_of_solvable_ker f _).symm
  obtain ⟨S,hS⟩ := c.join_sylow
  have hS' : (S : Subgroup H) = (pointSylow T v).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hS,map_subgroupOf_eq_of_le le_sup_right]
  have cov (X : Subgroup G) (hXH : X ≤ H) (hX : pointSylow T v ⋖ X) :
      (S : Subgroup H) ⋖ X.subgroupOf H := by
    apply (covBy_map_subtype_iff H _ _).mp
    rw [hS,map_subgroupOf_eq_of_le hXH]
    exact hX
  have neq (X Y : Subgroup G) (hX : X ≤ H) (hY : Y ≤ H) (hne : X ≠ Y) :
      X.subgroupOf H ≠ Y.subgroupOf H := by
    intro he
    have hh := congrArg (Subgroup.map H.subtype) he
    rw [map_subgroupOf_eq_of_le hX,map_subgroupOf_eq_of_le hY] at hh
    exact hne hh
  let eC := subgroupOfEquivOfLe (show C ≤ H from inf_le_left)
  let eqC := QuotientGroup.congr _ _ eC (pCore_map_iso 2 eC)
  have hcard : Nat.card (C.subgroupOf H ⧸ pCore 2 (C.subgroupOf H)) = 1008 :=
    (Nat.card_congr eqC.toEquiv).trans (m.plane_quotient_card_ten hd)
  have hs : Group.IsSolvable (A.subgroupOf H ⊔ B.subgroupOf H : Subgroup H) := by
    rw [←subgroupOf_sup hAH hBH]
    exact (solvable_subgroupOf_iff _ _ (sup_le hAH hBH)).mpr m.componentPointNode_pair_solvable
  have he : Group.IsSolvable (A.subgroupOf H ⊔ P.subgroupOf H : Subgroup H) ↔
      Group.IsSolvable (B.subgroupOf H ⊔ P.subgroupOf H : Subgroup H) := by
    rw [←subgroupOf_sup hAH hPH,←subgroupOf_sup hBH hPH,
      solvable_subgroupOf_iff _ _ (sup_le hAH hPH),
      solvable_subgroupOf_iff _ _ (sup_le hBH hPH)]
    exact hex
  apply BinaryLinear.FiveFlagGeometry.no_solvable_exchange_of_two_kernel
    m.joinAction m.joinAction_surjective m.joinAction_kernel_two S
    (C.subgroupOf H) (A.subgroupOf H) (B.subgroupOf H) (P.subgroupOf H)
    _ m.plane_maximal hcard
    (cov A hAH m.componentPointNode_covBy) (comap_mono m.componentPointNode_le_plane)
    (cov B hBH hB) (comap_mono hBC) (cov P hPH hP) (comap_mono hPC)
    (neq A B hAH hBH hAB) (neq A P hAH hPH hAP) (neq B P hBH hPH hBP) hs he
  rw [hS']
  exact comap_mono (le_inf le_sup_right m.pointSylow_centralizes_plane)

/-- The rank-ten case is removed without any extra preparation or model callback. -/
theorem LinearFiveData.dimension_five {c : Context D t v I} (m : LinearFiveData c) :
    letI := c.reduced.elementary
    Module.finrank (ZMod 2) (Additive (internalModule D v I)) = 5 :=
  m.dimension.resolve_right m.not_dimension_ten
end CFSG.Quasithin.Chapter10.PointControl.Constrained
