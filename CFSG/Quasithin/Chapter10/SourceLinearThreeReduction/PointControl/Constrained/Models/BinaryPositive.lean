module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.SevenMoved
public import Theory.SpecificGroups.SL2.BinaryLinearComparison

/-!
# Binary containing actors for every original natural cover

The actual original SL₃(2) quotient excludes the rank-two containing actors:
the local-component calculation would instead identify it with a binary SL₂.
This argument uses no inclusion of the original moved factor in VI. The
complete B.5.1 action sieve therefore retains only A₇ and binary-linear rows.

The exceptional A₇ four-space now reconstructs its original two-core quotient
through [VI,I], and the opposite cubic excludes that quotient. The marked
deleted-seven action is already excluded. Consequently every original natural
cover, with any fixed kernel, has a binary SL₄(2) or SL₅(2) containing actor.
The exact source conclusion, moved space and central quotient are retained.

Excluding these binary actors for positive original covers, general quiet
preparation and the retained four-natural row remain with the final assembly
owner qt-d-10-nona5-point-constrained.
Source: Aschbacher–Smith 10.2.9, printed pp.751–752.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open ChapterB.QuasisimpleSource Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- An actual binary-three original quotient excludes all four rank-two
containing actions without a moved-span premise. -/
theorem Context.no_rankTwo_action_of_binaryThree_quotient (c : Context D t v I)
    (af : ActionFacts c) (e : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
    ∀ (N : Subgroup (ActionQuotient (internalModule D v I))) (_hAN : A ≤ N)
      (s : MovedSection ((action (internalModule D v I)).comp N.subtype) (A.subgroupOf N)),
      ¬ RankTwoAction s := by
  let := c.reduced.normal
  let := c.reduced.elementary
  dsimp only
  intro N hAN s hs
  let d := (subgroupOfEquivOfLe hAN).symm
  have no_rank_one {F : Type} [Field F] [Finite F] [CharP F 2]
      (f : (L ⧸ pCore 2 L) ≃* SL(2,F)) : False :=
    Matrix.SL2.binary_not_equiv_linear_three (F := F) (E := ZMod 2) (n := 1)
      (by decide) (by simp) (f.symm.trans e)
  cases hs with
  | linearThree F hn E =>
    obtain ⟨f⟩ := c.rank_one_quotient_of_linear_three af F.card_eq hn (d.trans E.groupEquiv)
    exact no_rank_one f
  | doubleThree F hn E =>
    obtain ⟨f⟩ := c.rank_one_quotient_of_linear_three af F.card_eq hn (d.trans E.groupEquiv)
    exact no_rank_one f
  | symplectic F hn E =>
    obtain ⟨f⟩ := c.rank_one_quotient_of_symplectic_four af F.card_eq hn (d.trans E.groupEquiv)
    exact no_rank_one f
  | g2 F hn E =>
    have hF : 2 < Nat.card F.Carrier := by
      rw [F.card_eq]
      have := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ F.degree)
      omega
    obtain ⟨f⟩ := c.rank_one_quotient_of_g2 af hF (d.trans E.groupEquiv)
    exact no_rank_one f

/-- The original binary-three quotient retains the complete source conclusion
and every containing action marking, without any full-span hypothesis. -/
theorem Context.binary_or_seven_action_of_binaryThree_quotient (c : Context D t v I) (a : ActionFacts c)
    (original : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
    let N := offenderSubgroup (action (internalModule D v I))
    ∃ h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        ((action (internalModule D v I)).comp N.subtype) (A.subgroupOf N),
      BinaryOrSevenAction h.sectionData := by
  let H := pointJoin T v I
  let U := internalModule D v I
  let := c.reduced.normal
  let := c.reduced.elementary
  let K := I.subgroupOf H
  let q := actionMk U
  let A := K.map q
  let N := offenderSubgroup (action U)
  let C := A.subgroupOf N
  let B := ((L.subgroupOf H).map q).subgroupOf A
  obtain ⟨hA,hAN,_,_,_,⟨h⟩⟩ := a.classification
  let e : A ≃* C := (subgroupOfEquivOfLe hAN).symm
  let : IsQuasisimple A := hA
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv e
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]
    exact Group.isSolvable_of_comm (fun x y => by
      have hx : x = 1 := Subtype.ext (mem_bot.mp x.property)
      rw [hx,one_mul,mul_one])
  obtain ⟨hp,R,_,hl⟩ := a.small_local
  let S := R.mapSurjective (q.subgroupMap_surjective K)
  have hl' := Chapter1.Section02.localCComponents_map_of_solvable_ker
    (G := A) (G' := C) (B := B) (S := (S : Subgroup A)) hl e.toMonoidHom
  have hp' : B.map e.toMonoidHom ≠ ⊤ := by
    intro he
    exact hp.ne (map_injective e.injective (he.trans (map_top_of_surjective _ e.surjective).symm))
  refine ⟨h,?_⟩
  exact (containing_action_of_source_case _ C h.sectionData h.clause_one
    (S.mapSurjective (f := e.toMonoidHom) e.surjective) _ hl' hp').resolve_left
      (c.no_rankTwo_action_of_binaryThree_quotient a original N hAN h.sectionData)

/-- Positive as well as zero-kernel natural covers leave only binary-linear
containing actors, with the complete B.5.1 source action retained. -/
theorem Context.binary_source_action_of_binaryThreeNatural (c : Context D t v I)
    (hmodel : Selection.BinaryThreeNatural D) :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
    let N := offenderSubgroup (action (internalModule D v I))
    ∃ h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        ((action (internalModule D v I)).comp N.subtype) (A.subgroupOf N),
      BinaryOrSevenAction h.sectionData ∧
        ∃ d, (d = 4 ∨ d = 5) ∧ Nonempty (A ≃* SL(d,ZMod 2)) := by
  let := c.reduced.normal
  let := c.reduced.elementary
  let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
  let N := offenderSubgroup (action (internalModule D v I))
  have a := c.actionFacts_of_binaryThreeNatural hmodel
  have hAN : A ≤ N := a.classification.2.1
  let f : A ≃* A.subgroupOf N := (subgroupOfEquivOfLe hAN).symm
  let original := hmodel.choose
  obtain ⟨h,hs⟩ := c.binary_or_seven_action_of_binaryThree_quotient a original
  refine ⟨h,hs,?_⟩
  cases hs with
  | sevenFour _ hi E hd =>
    exact (c.no_seven_four_section_of_binaryThreeNatural hmodel N hAN h.sectionData E hi hd).elim
  | sevenDeleted _ _ E =>
    exact (c.no_deletedSeven_source_section a h.sectionData ⟨E⟩).elim
  | linear d hd _ _ E => exact ⟨d,hd,⟨f.trans E.groupEquiv⟩⟩
  | orthogonalSix _ _ E => exact ⟨4,Or.inl rfl,
      ⟨((f.trans E.groupEquiv).trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two).trans
        (_root_.BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))⟩⟩
  | symmetricEight _ _ E => exact ⟨4,Or.inl rfl,
      ⟨((f.trans E.subgroupEquiv).trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two).trans
        (_root_.BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))⟩⟩
  | exteriorFive _ _ E _ => exact ⟨5,Or.inr rfl,⟨f.trans E⟩⟩
  | naturalDual d hd E => exact ⟨d,hd,⟨f.trans E.some.groupEquiv⟩⟩
  | repeatedNatural d _ hd _ _ E => exact ⟨d,hd,⟨f.trans E.some.groupEquiv⟩⟩

/-- No A₇ containing actor occurs for any original natural cover. -/
theorem Context.no_seven_actor_of_binaryThreeNatural (c : Context D t v I)
    (hmodel : Selection.BinaryThreeNatural D) :
    letI := c.reduced.normal
    ∀ (_E : ((I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))) ≃*
      alternatingGroup (Fin 7)), False := by
  let := c.reduced.normal
  let := c.reduced.elementary
  intro E
  obtain ⟨_,_,d,hd,⟨f⟩⟩ := c.binary_source_action_of_binaryThreeNatural hmodel
  have hc := Nat.card_congr (f.symm.trans E).toEquiv
  rw [_root_.BinaryLinear.card_SL,nat_card_alternatingGroup] at hc
  rcases hd with rfl | rfl <;>
    norm_num [_root_.BinaryLinear.order,Fin.prod_univ_succ,Nat.factorial] at hc
end CFSG.Quasithin.Chapter10.PointControl.Constrained
