module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.RankTwoReduction
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.RankOneSpan
public import Theory.SpecificGroups.Alternating.SevenRankOneSection
public import Theory.SpecificGroups.SL2.BinaryLinearComparison
public import Theory.SpecificGroups.SL2.CardFourEquiv

/-!
# Complete exclusion of the original rank-one natural-cover branch

The original marking supplies full moved-span generation, preparation and
the faithful FF action, retaining any fixed kernel. The torus reduction
leaves A₇ or an original SL₃(2) quotient. A binary rank-one quotient in a
proper subgroup of A₇ forces field order four and hence the forbidden A₅
isomorphism. Binary SL₂ is never SL₃(2), excluding the second alternative.

This proves the contradiction for every marked original rank-one cover and
applies it to Selection.RankOneNatural. The local Thompson-moving branch
therefore has the original binary-three quotient. General quiet recognition,
the retained four-natural row, and the binary-three endgame reduction remain
with qt-d-10-nona5-point-constrained.
Source: Aschbacher–Smith 10.2.9, printed pp.751–752.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open ChapterB.QuasisimpleSource Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- A₇ cannot contain the actual smaller image of a non-A₅ binary rank-one quotient. -/
theorem Context.no_seven_actor_of_rankOne_quotient (c : Context D t v I) (a : ActionFacts c)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    letI := c.reduced.normal
    ∀ (_E : ((I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))) ≃*
      alternatingGroup (Fin 7)), False := by
  let := c.reduced.normal
  intro E
  let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
  let B := ((L.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))).subgroupOf A
  obtain ⟨hp,_,_⟩ := c.marked_small_image_local a E
  obtain ⟨b⟩ := c.small_local_quotient a
  let j : B ≃* B.map E.toMonoidHom := E.subgroupMap B
  let eB := ((QuotientGroup.congr _ _ j (pCore_map_iso 2 j)).symm.trans b).trans e
  have hn2 := alternatingGroup.SevenRankOneSection.degree_eq_two hF hn
    (B.map E.toMonoidHom) hp _ eB
  have hfour : Nat.card F = 4 := by rw [hF,hn2]; norm_num
  obtain ⟨f⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hfour
  exact c.nonA5 ⟨(e.trans (Theory.PSL2.sl2QuotientEquiv F)).trans f⟩

local instance {F : Type*} [Field F] [CharP F 2] : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- The entire original rank-one natural-cover branch is excluded, including every fixed kernel. -/
theorem Context.no_rankOne_cover (c : Context D t v I)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) : False := by
  have a := c.actionFacts_of_rankOne_cover n hn hF e s
  rcases c.seven_actor_or_binaryThree_of_moved_le a
      (c.moved_le_of_rankOne_cover n hn hF e s) with hseven | hthree
  · exact c.no_seven_actor_of_rankOne_quotient a hn hF e hseven.some
  · exact Matrix.SL2.binary_not_equiv_linear_three (F := F) (E := ZMod 2) (n := 1)
      (by decide) (by simp) (e.symm.trans hthree.some)

/-- Actual application to the existing original source-row contract. -/
theorem Context.no_rankOneNatural (c : Context D t v I) : ¬ Selection.RankOneNatural D := by
  rintro ⟨n,hn,e,⟨s⟩⟩
  let : NeZero n := ⟨by omega⟩
  exact c.no_rankOne_cover n hn (GaloisField.card 2 n (by omega)) e s

/-- After the rank-one exclusion, local Thompson movement forces the original SL₃(2) quotient. -/
theorem Context.binaryThree_of_local_thompson_moves (c : Context D t v I)
    (hJ : ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G)) :
    Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) := by
  exact (Selection.ModuleChoice.rankOneNatural_or_binaryThree_component D
    (fun hn => c.escaping.t_not_normalizes (hn c.escaping.t_mem)) c.nonA5 hJ).resolve_left
      c.no_rankOneNatural

end CFSG.Quasithin.Chapter10.PointControl.Constrained
