module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.ActionSieve
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.OriginalQuotients
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedRestriction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedSection

/-!
# Removing all four rank-two containing actions

The B.5.1 section lives over the offender subgroup of the literal action
quotient. Comparing it to the canonical moved section transports its
central quotient and moved-space coordinates without deleting fixed vectors.
Parabolic placement recovers the original SL₂ quotient over the same field,
and the proved scalar obstruction excludes SL₃, doubled SL₃, Sp₄ and G₂.

The resulting source conclusion retains all six B.5.1 clauses and the
actual A₇ or binary-linear action. The only additional premise is inclusion
of the original moved subgroup in VI. The constrained assembly owner retains
its general proof; Models.RankOneExclusion discharges it for natural covers.
Source: Aschbacher–Smith 10.2.9, printed pp.751–752.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open ChapterB.QuasisimpleSource Chapter3.Section02 ChapterB.InternalThompsonAction

private def composeAction {A B C U V W : Type*} [Group A] [Group B] [Group C]
    [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) A U} {σ : Representation (ZMod 2) B V}
    {τ : Representation (ZMod 2) C W} (e : ActionEquiv ρ σ) (f : ActionEquiv σ τ) :
    ActionEquiv ρ τ where
  groupEquiv := e.groupEquiv.trans f.groupEquiv
  linearEquiv := e.linearEquiv.trans f.linearEquiv
  intertwines g v := by
    change f.linearEquiv (e.linearEquiv (ρ g v)) = _
    rw [e.intertwines,f.intertwines]
    rfl

private def liftCentralAction
    {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) Q V} {A N : Subgroup Q} (hAN : A ≤ N)
    (s : MovedSection (ρ.comp N.subtype) (A.subgroupOf N))
    (r : MovedSection ρ A) :
    ActionEquiv (r.action.comp A.subtype) (s.action.comp (A.subgroupOf N).subtype) := by
  apply s.componentEmbeddingEquiv r (subgroupOfEquivOfLe hAN).symm LinearMap.id
    (fun _ _ h => h)
  · intros; rfl
  · rw [moved_comp_map,map_subgroupOf_eq_of_le hAN,Submodule.map_id]

private def liftMovedAction
    {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) Q V} {A N : Subgroup Q} (hAN : A ≤ N)
    (s : MovedSection (ρ.comp N.subtype) (A.subgroupOf N))
    (r : MovedSection ρ A) :
    ActionEquiv (r.space.toRepresentation.comp A.subtype)
      (s.space.toRepresentation.comp (A.subgroupOf N).subtype) where
  groupEquiv := (subgroupOfEquivOfLe hAN).symm
  linearEquiv := LinearEquiv.ofEq _ _ (by
    rw [r.space_eq,s.space_eq,moved_comp_map,map_subgroupOf_eq_of_le hAN])
  intertwines g v := by apply Subtype.ext; rfl

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- The four rank-two source actions are excluded on the actual restricted FF section. -/
theorem Context.no_rankTwo_action_of_moved_le (c : Context D t v I) (a : ActionFacts c)
    (hspan : ⁅D.fullModule,L⁆ ≤ orbitModule D v I) :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
    ∀ (N : Subgroup (ActionQuotient (internalModule D v I))) (_hAN : A ≤ N)
      (s : MovedSection ((action (internalModule D v I)).comp N.subtype) (A.subgroupOf N)),
      ¬ RankTwoAction s := by
  let H := pointJoin T v I
  let U := internalModule D v I
  let := c.reduced.normal
  let := c.reduced.elementary
  let K := I.subgroupOf H
  let q := actionMk U
  let A := K.map q
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le I.le_normalizer (inf_le_right.trans c.escaping.normalizes))
  let : A.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  dsimp only
  intro N hAN s hs
  let r := MovedSection.ofNormal (action U) A
  cases hs with
  | linearThree F hn E =>
    let E' := composeAction (liftCentralAction hAN s r) E
    obtain ⟨e⟩ := c.rank_one_quotient_of_linear_three a F.card_eq hn E'.groupEquiv
    exact c.no_linearThree_source_section_of_local a F.card_eq hn e hspan r E'
  | doubleThree F hn E =>
    let E' := composeAction (liftMovedAction hAN s r) E
    obtain ⟨e⟩ := c.rank_one_quotient_of_linear_three a F.card_eq hn E'.groupEquiv
    exact c.no_repeatedThree_source_section_of_local a F.card_eq hn e hspan r E'
  | symplectic F hn E =>
    let E' := composeAction (liftCentralAction hAN s r) E
    obtain ⟨e⟩ := c.rank_one_quotient_of_symplectic_four a F.card_eq hn E'.groupEquiv
    exact c.no_symplecticFour_source_section_of_local a F.card_eq hn e hspan r E'
  | g2 F hn E =>
    let E' := composeAction (liftCentralAction hAN s r) E
    have hF : 2 < Nat.card F.Carrier := by
      rw [F.card_eq]
      have := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ F.degree)
      omega
    obtain ⟨e⟩ := c.rank_one_quotient_of_g2 a hF E'.groupEquiv
    exact c.no_g2_source_section_of_local a F.card_eq hn e hspan r E'

/-- The actual source conclusion retains only A₇ and binary-linear actions after the torus argument. -/
theorem Context.binary_or_seven_action_of_moved_le (c : Context D t v I) (a : ActionFacts c)
    (hspan : ⁅D.fullModule,L⁆ ≤ orbitModule D v I) :
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
      (c.no_rankTwo_action_of_moved_le a hspan N hAN h.sectionData)
/-- The full-span branch has only an A₇ actor or an original binary-three quotient. -/
theorem Context.seven_actor_or_binaryThree_of_moved_le (c : Context D t v I)
    (a : ActionFacts c) (hspan : ⁅D.fullModule,L⁆ ≤ orbitModule D v I) :
    letI := c.reduced.normal
    Nonempty (((I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))) ≃*
      alternatingGroup (Fin 7)) ∨ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) := by
  let := c.reduced.normal
  let := c.reduced.elementary
  obtain ⟨h,hs⟩ := c.binary_or_seven_action_of_moved_le a hspan
  let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
  let N := offenderSubgroup (action (internalModule D v I))
  let e : A ≃* A.subgroupOf N := (subgroupOfEquivOfLe a.classification.2.1).symm
  rcases hs.actor with hseven | ⟨d,hd,hlinear⟩
  · exact Or.inl ⟨e.trans hseven.some⟩
  · exact Or.inr (c.binary_three_quotient_of_binary_containing a hd (e.trans hlinear.some))

end CFSG.Quasithin.Chapter10.PointControl.Constrained
