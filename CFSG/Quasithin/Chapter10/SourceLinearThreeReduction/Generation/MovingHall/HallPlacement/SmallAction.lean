module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.HallPlacement.ComparisonQuotient
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BinaryIntrinsicQuotients
public import Theory.SpecificGroups.SL2.BinaryLinearComparison
public import Theory.SpecificGroups.Classical.BinaryLinearThreeRank
public import Theory.SpecificGroups.Alternating.SevenRankOneSection
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.HallPlacement.SingleFive

/-!
# Small containing actions in the original moving comparison

The original smaller quotient is binary SL₂. Binary SL₄(2) and SL₅(2)
local components have higher linear quotients, excluded by the rank-one
order and odd-rank bounds. A proper smaller image inside A₇ forces field
order four. Transport through the actual restricted action gives an A₅
quotient of the original comparison and the literal Hall three-group bound.
This direct bound does not assert Hall placement.

Source: Aschbacher–Smith 10.2.3, printed pp.745–746; A.3.12 and B.5.1.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
open Chapter3.Section02 ChapterB.InternalThompsonAction ChapterA.Section03
open ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction ChapterE.ThompsonAction
open ChapterC.RankOne.ChiProduct.SelectedRankOne
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {H : Subgroup G} {B : Subgroup H} {ctx : Context D H B}

/-- No local component of the binary four- or five-dimensional group has a binary rank-one two-core quotient. -/
private theorem binary_local_not_rank_one
    {X E : Type*} [Group X] [Finite X] [Field E] [Finite E] [CharP E 2]
    (S : Sylow 2 X) (K : Subgroup X) (hK : K ∈ localCComponents S)
    (eK : (K ⧸ pCore 2 K) ≃* SL(2,E))
    (d : ℕ) (hd : d = 4 ∨ d = 5) (a : X ≃* SL(d,ZMod 2)) : False := by
  let b := a.trans (BinaryLinear.OuterCyclic.slEquivLinear d)
  let : Group.IsSolvable b.toMonoidHom.ker := by
    rw [b.toMonoidHom.ker_eq_bot_iff.mpr b.injective]
    exact Group.isSolvable_of_comm (fun _ _ => Subsingleton.elim _ _)
  have hl := Chapter1.Section02.localCComponents_map_of_solvable_ker hK b.toMonoidHom
  obtain ⟨m,hm,hmd,⟨j⟩⟩ := SourceEmbeddings.BinaryIntrinsic.local_twoCore_quotient
    d (by omega) (S.mapSurjective b.surjective) (K.map b.toMonoidHom) hl
  let k := b.subgroupMap K
  let kq := QuotientGroup.congr _ _ k (pCore_map_iso 2 k)
  let r : SL(2,E) ≃* SL(m,ZMod 2) :=
    eK.symm.trans (kq.trans (j.trans (BinaryLinear.OuterCyclic.slEquivLinear m).symm))
  by_cases h3 : m = 3
  · subst m
    exact Matrix.SL2.binary_not_equiv_linear_three (n := 1) (by decide) (by simp) r
  · have hl := Matrix.SL2.binary_odd_primeRank_le_one (F := E) (by decide : Odd 3)
    rw [primeRank_equiv 3 r] at hl
    have hr := Theory.SpecificGroups.Classical.BinaryLinearThreeRank.two_le_primeRank
      (show 4 ≤ m by omega)
    omega

/-- A proper small containing action forces the original comparison quotient to be A₅. -/
theorem ComparisonConfiguration.single_a5_of_small_action
    (c : ComparisonConfiguration D ctx) (hsingle : c.component = pResidual 2 H)
    (hqs : IsQuasisimple (c.overcomponent ⧸ pCore 2 c.overcomponent))
    (hproper : c.component.map H.subtype < c.overcomponent)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hsmall : letI := (c.orbit_reduced D).normal
      SmallComparisonAction
        ((c.overcomponent.subgroupOf (c.join D)).map (actionMk (c.orbit D)))) :
    Nonempty ((c.component ⧸ pCore 2 c.component) ≃* alternatingGroup (Fin 5)) := by
  let J := c.join D
  let I := c.overcomponent.subgroupOf J
  let := (c.orbit_reduced D).normal
  let q := actionMk (c.orbit D)
  let A := I.map q
  let K := ((c.component.map H.subtype).subgroupOf J).map q
  let Kb := K.subgroupOf A
  have hKA : K ≤ A := map_mono (comap_mono c.component_le)
  have hp : Kb ≠ ⊤ := by
    intro ht
    have he : K = A := le_antisymm hKA (subgroupOf_eq_top.mp ht)
    exact hproper.ne (c.single_eq_of_action_image_eq D hsingle hqs he)
  obtain ⟨S,_,hl⟩ := c.single_small_image_local D hsingle
  let Sb := S.mapSurjective (q.subgroupMap_surjective I)
  obtain ⟨E,hE,⟨r⟩⟩ := c.single_linear_quotient D hsingle n hn hF e mark
  obtain ⟨k⟩ := c.small_local_quotient D n hn hF e mark
  let rK : (Kb ⧸ pCore 2 Kb) ≃* SL(2,E.Carrier) := k.trans r
  have hm : Nonempty (A ≃* alternatingGroup (Fin 7)) ∨
      ∃ d : ℕ, (d = 4 ∨ d = 5) ∧ Nonempty (A ≃* SL(d,ZMod 2)) :=
    SmallComparisonAction.cases hsmall
  rcases hm with ha | hd
  · obtain ⟨a⟩ := ha
    let : Group.IsSolvable a.toMonoidHom.ker := by
      rw [a.toMonoidHom.ker_eq_bot_iff.mpr a.injective]
      exact Group.isSolvable_of_comm (fun _ _ => Subsingleton.elim _ _)
    let b := a.subgroupMap Kb
    let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
    have hp' : Kb.map a.toMonoidHom ≠ ⊤ := by
      intro ht
      apply hp
      apply map_injective (f := a.toMonoidHom) a.injective
      rw [ht,map_top_of_surjective _ a.surjective]
    have hdegree := alternatingGroup.SevenRankOneSection.degree_eq_two E.card_eq hE
      (Kb.map a.toMonoidHom) hp' (pCore 2 (Kb.map a.toMonoidHom)) (bq.symm.trans rK)
    have hcE : Nat.card E.Carrier = 4 := by rw [E.card_eq,hdegree]; norm_num
    obtain ⟨a5⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hcE
    exact ⟨r.trans ((Theory.PSL2.sl2QuotientEquiv E.Carrier).trans a5)⟩
  · obtain ⟨d,hd,⟨a⟩⟩ := hd
    exact (binary_local_not_rank_one Sb Kb hl rK d hd a).elim

/-- The small-action branch gives the required bound for the literal Hall subgroup. -/
theorem ComparisonConfiguration.hall_three_of_single_small_action
    (c : ComparisonConfiguration D ctx) (hsingle : c.component = pResidual 2 H)
    (hqs : IsQuasisimple (c.overcomponent ⧸ pCore 2 c.overcomponent))
    (hproper : c.component.map H.subtype < c.overcomponent)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hsmall : letI := (c.orbit_reduced D).normal
      SmallComparisonAction
        ((c.overcomponent.subgroupOf (c.join D)).map (actionMk (c.orbit D)))) :
    IsPGroup 3 B :=
  c.hall_isThreeGroup_of_single_a5 D hsingle
    (c.single_a5_of_small_action D hsingle hqs hproper n hn hF e mark hsmall).some
end CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
