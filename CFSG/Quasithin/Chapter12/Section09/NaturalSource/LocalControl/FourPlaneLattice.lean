module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PlaneReduction
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianParabolics
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups.FourThreeSpaceQuotient

/-!
# The degree-four plane-overgroup lattice

If the original plane-centralizer bound fails, its actual plane join Y
strictly contains the last-node parabolic, which strictly contains T.
In either binary point-model row, the three-rank bound and the Sylow-flag
lattice identify Y/O₂(Y) with GL₃(2), using the literal intrinsic core.
In the GL₄(2) row Y is maximal in K₁T; irreducibility of L₁ on V/V₁
then makes Y join L₁ equal K₁T. The existing point-model list leaves only
the A₇ row outside this calculation.

The quotient transport uses the original Sylow's inner action and the
specified point-component isomorphism. This is an overgroup calculation;
the plane-module contradiction and the nonabelian catalogue are separate
obligations in the natural-branch assembly.

Source: Aschbacher--Smith, 12.9.7, refs/quasithin.pdf, printed p.862.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag
open BinaryLinear.OuterCyclic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original last-node parabolic properly contains the full Sylow. -/
theorem four_last_parabolic_gt_sylow
    {K : GroupClass.{u}} (h : HigherRankHypothesis K T L V 4)
    (F : InvariantFlag T V 4) :
    (T : Subgroup G) < F.orderedParabolic L 3 := by
  let := h.chosen.elementary
  obtain ⟨β,e,b,_,_,hS,hP⟩ := F.exists_marked_naturalFlag L h.chosen.normalizes h.full_L_action
  refine lt_of_le_of_ne (F.sylow_le_orderedParabolic L 3) ?_
  intro he
  have he' := congrArg (fun A : Subgroup G =>
    ((A.subgroupOf (L ⊔ (T : Subgroup G))).map (F.naturalFlagAction L h.chosen.normalizes)).map
      e.toMonoidHom) he
  rw [F.naturalOrderedParabolic_image L h.chosen.normalizes h.full_L_action] at he'
  change (F.naturalFlagSylow L h.chosen.normalizes h.full_L_action : Subgroup (MulAut V)).map
    e.toMonoidHom = _ at he'
  have hp : (F.naturalOrderedParabolic 3).map e.toMonoidHom =
      BinaryLinear.InvariantNodeActions.minimalParabolic b (2 : Fin 3) := hP (2 : Fin 3)
  rw [hS,hp] at he'
  have hh := BinaryLinear.CubicSylowGeneration.minimalParabolic_index b (2 : Fin 3)
  rw [he',relIndex_self] at hh
  contradiction

/-- Failure of the plane bound supplies two strict inclusions above the same T. -/
theorem four_plane_escape_chain
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L)
    (hfail : ¬ centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G)) :
    (T : Subgroup G) < F.orderedParabolic L 3 ∧
      F.orderedParabolic L 3 < planeCentralizerJoin F C := by
  have hJH := F.orderedParabolic_le_H (by decide : 2 ≤ 4) L (by decide : 2 ≤ 3)
  have hJG : F.orderedParabolic L 3 ≤ F.Gi 2 :=
    inf_le_right.trans (iInf_le_of_le 2 (iInf_le_of_le (by decide) le_rfl))
  have hJY : F.orderedParabolic L 3 ≤ planeCentralizerJoin F C := by
    rw [planeCentralizerJoin_eq_point_plane h (Or.inl rfl) earlier F hab C]
    exact le_inf hJH hJG
  have hJP : F.orderedParabolic L 3 ≤ F.Li L 1 ⊔ (T : Subgroup G) := by
    rw [Components.point_residual_sylow_eq_intersection h earlier F]
    exact le_inf inf_le_left hJH
  exact ⟨four_last_parabolic_gt_sylow h F,lt_of_le_of_ne hJY (fun he =>
    (plane_centralizer_escape_join h (Or.inl rfl) earlier F hab C hfail).1
      (he.symm ▸ hJP))⟩

/-- The original point join has the same binary quotient as its component. -/
theorem four_point_join_binary_equiv
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (C : ComponentGeometry F L)
    {d : ℕ} (hd : d = 4 ∨ d = 5)
    (hm : ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) d 2) :
    Nonempty (((C.K1 ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (C.K1 ⊔ (T : Subgroup G) : Subgroup G)) ≃* LinearGroup d) := by
  obtain ⟨k,_,_,hcard,⟨e₀⟩⟩ := hm
  let ek := Theory.SpecificGroups.SymplecticSix.fieldEquivZModTwo k hcard
  let e := (e₀.trans (Atlas.fieldEquivPSL d ek)).trans
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by omega : 0 < d))
  have hz : center (C.K1 ⧸ pCore 2 C.K1) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    let eS := e.trans (slEquivLinear d).symm
    have he : eS x ∈ center (Matrix.SpecialLinearGroup (Fin d) (ZMod 2)) :=
      (centerCongr eS ⟨x,hx⟩).property
    rw [binary_center_eq_bot (by omega),mem_bot] at he
    exact mem_bot.mpr (eS.map_eq_one_iff.mp he)
  let hTN := (F.invariant 1).trans
    ((normal_subgroupOf_iff_le_normalizer C.point_le).mp C.normal)
  have hi := binary_sylow_acts_inner h (Or.inl rfl) earlier F C hd
    (show ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) d 2 from
      ⟨k,inferInstance,inferInstance,hcard,⟨e₀⟩⟩)
  exact ⟨ (pCoreJoinQuotientEquivOfInner C.K1 (T : Subgroup G)
    hTN T.isPGroup' hz hi).trans e⟩

/-- In either binary point model, the original escaping Y has quotient GL₃(2). -/
theorem four_plane_escape_binary_structure
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L)
    (hfail : ¬ centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G))
    {d : ℕ} (hd : d = 4 ∨ d = 5)
    (hm : ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) d 2) :
    Nonempty (((planeCentralizerJoin F C) ⧸ pCore 2 (planeCentralizerJoin F C)) ≃*
      LinearGroup 3) ∧
      (d = 4 → planeCentralizerJoin F C ⊔ F.Li L 1 = C.K1 ⊔ (T : Subgroup G)) := by
  let X := C.K1 ⊔ (T : Subgroup G)
  let Y := planeCentralizerJoin F C
  let J := F.orderedParabolic L 3
  obtain ⟨hTJ,hJY⟩ := four_plane_escape_chain h earlier F hab C hfail
  have hYX : Y ≤ X := inf_le_left
  have hJX : J ≤ X := hJY.le.trans hYX
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  obtain ⟨eX⟩ := four_point_join_binary_equiv h earlier F C hd hm
  let q := eX.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hq : Function.Surjective q := eX.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 q.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ eX.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hTJ' : ((T.subtype hTX) : Subgroup X) < J.subgroupOf X := by
    refine lt_of_le_of_ne (comap_mono hTJ.le) ?_
    intro he
    have hh := congrArg (map X.subtype) he
    change ((T : Subgroup G).subgroupOf X).map X.subtype =
      (J.subgroupOf X).map X.subtype at hh
    rw [map_subgroupOf_eq_of_le hTX,map_subgroupOf_eq_of_le hJX] at hh
    exact hTJ.ne hh
  have hJY' : J.subgroupOf X < Y.subgroupOf X := by
    refine lt_of_le_of_ne (comap_mono hJY.le) ?_
    intro he
    have hh := congrArg (map X.subtype) he
    rw [map_subgroupOf_eq_of_le hJX,map_subgroupOf_eq_of_le hYX] at hh
    exact hJY.ne hh
  have hr : primeRank 3 (Y.subgroupOf X) ≤ 1 := by
    rw [primeRank_equiv 3 (subgroupOfEquivOfLe hYX)]
    exact planeCentralizerJoin_three_rank h (Or.inl rfl) earlier F hab C
  obtain ⟨a⟩ := BinaryLinear.SylowFlagOvergroups.binary_quotient_linearThree_of_two_kernel_chain
    hd q hq hk (T.subtype hTX) (J.subgroupOf X) (Y.subgroupOf X) hTJ' hJY' hr
  let c := subgroupOfEquivOfLe hYX
  refine ⟨⟨(QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).symm.trans a⟩,?_⟩
  intro hd4
  subst d
  have hc := BinaryLinear.SylowFlagOvergroups.four_coatom_of_two_kernel_chain
    q hq hk (T.subtype hTX) (J.subgroupOf X) (Y.subgroupOf X) hTJ' hJY' hr
  have hLnot : ¬ F.Li L 1 ≤ F.Gi 2 := by
    let := h.chosen.elementary
    intro hL
    rcases F.localKernel_irreducible L (by decide : 2 ≤ 4) h.chosen.normalizes
      (fun _ => ⟨h.naturalMarking⟩) (F.Vi 2) (F.monotone (by decide)) (F.le_seed 2) hL with he | he
    · have hh := congrArg (fun A : Subgroup G => Nat.card A) he
      rw [F.card 2 (by decide),F.card 1 (by decide)] at hh
      norm_num at hh
    · have hh := congrArg (fun A : Subgroup G => Nat.card A) (he.trans F.last.symm)
      rw [F.card 2 (by decide),F.card 4 (by decide)] at hh
      norm_num at hh
  have hLX : F.Li L 1 ≤ X := C.contains.trans le_sup_left
  have hHX : Y ⊔ F.Li L 1 ≤ X := sup_le hYX hLX
  have hlt : Y.subgroupOf X < (Y ⊔ F.Li L 1).subgroupOf X := by
    refine lt_of_le_of_ne (comap_mono le_sup_left) ?_
    intro he
    have hh := congrArg (map X.subtype) he
    rw [map_subgroupOf_eq_of_le hYX,map_subgroupOf_eq_of_le hHX] at hh
    exact hLnot ((le_sup_right.trans hh.ge).trans (planeCentralizerJoin_placements h F C).2)
  have he := congrArg (map X.subtype) (hc.2 _ hlt)
  rw [map_subgroupOf_eq_of_le hHX,←MonoidHom.range_eq_map,range_subtype] at he
  exact he


/-- The original model list leaves only the A₇ point row outside the proved
three-space quotient calculation. -/
theorem four_plane_escape_quotient_or_seven
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L)
    (hfail : ¬ centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G)) :
    Chapter1.Section02.LocalModels.IsAlternating (C.K1 ⧸ pCore 2 C.K1) 7 ∨
      Nonempty (((planeCentralizerJoin F C) ⧸ pCore 2 (planeCentralizerJoin F C)) ≃*
        LinearGroup 3) := by
  rcases point_models_of_abelian h (Or.inl rfl) earlier F hab C with h7 | h4 | h5
  · exact Or.inl h7
  · exact Or.inr (four_plane_escape_binary_structure h earlier F hab C hfail (Or.inl rfl) h4).1
  · exact Or.inr (four_plane_escape_binary_structure h earlier F hab C hfail (Or.inr rfl) h5).1

end CFSG.Quasithin.Chapter12.Section09.NaturalSource
