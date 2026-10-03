module

public import Stellmacher.SectionNine.LemmaNineSeven
public import Stellmacher.SectionNine.NineSixSmallModule

/-!
# The predecessor coatom contradiction in (9.10)

At critical length greater than three, a conjugate of the third module by
an element of the first stabilizer has no subgroup of at least half its order contained in
the first module. The original exact-index-two theorem remains a wrapper. This applies to the actual predecessor obtained from the
normalized extraction, once (9.4) forces its proposed coatom into that module.

Map the first/third intersection by the same conjugating automorphism.
The hypothetical subgroup gives a lower bound of half the module order for
this intersection. Local transitivity identifies the two module orders,
and critical minimality makes their intersection proper. Its finite relative
index is therefore exactly two. The genuine ambient (9.7) then forces the
critical length to be three, contradicting the hypothesis.

Source: Stellmacher (9.10), printed p.57, the contradiction immediately before
assertion (5). No pending (9.4) conclusion is assumed in proving this standalone
obstruction; the subgroup containment is what the theorem rules out.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem nine_ten_predecessor_large_subgroup_not_le_first
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (third : ctx.Γ.Vertex)
    (hthird : IsCriticalPathOffset ctx.Γ ctx.criticalPath 3 third)
    (conjugator : G) (hconjugator : conjugator ∈ GAt ctx.Γ ctx.criticalPath.firstStep)
    (K : Subgroup G)
    (hK : K ≤ VAt ctx.Γ (ctx.Γ.act conjugator third))
    (hindex : Nat.card (VAt ctx.Γ (ctx.Γ.act conjugator third)) ≤ 2 * Nat.card K) :
    ¬ K ≤ VAt ctx.Γ ctx.criticalPath.firstStep := by
  intro hfirst
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let first := VAt Γ cp.firstStep
  let other := VAt Γ third
  let common : Subgroup G := first ⊓ other
  let c := (MulAut.conj conjugator⁻¹).toMonoidHom
  have hc : Function.Injective c := (MulAut.conj conjugator⁻¹).injective
  have hfix : Γ.act conjugator cp.firstStep = cp.firstStep :=
    (Set.ext_iff.mp (Γ.stabilizer_def cp.firstStep) conjugator).mp hconjugator
  have hfirstMap : first.map c = first := by
    change (v Γ cp.firstStep).map c = v Γ cp.firstStep
    rw [← v_act Γ conjugator cp.firstStep, hfix]
  have hotherMap : other.map c = VAt Γ (Γ.act conjugator third) := by
    exact (v_act Γ conjugator third).symm
  have hcommonMap : common.map c = first ⊓ VAt Γ (Γ.act conjugator third) := by
    rw [Subgroup.map_inf _ _ _ hc, hfirstMap, hotherMap]
  have hKcommon : K ≤ common.map c := by
    rw [hcommonMap]
    exact le_inf hfirst hK
  have hKcard : Nat.card K ≤ Nat.card common := by
    have h := Nat.card_le_card_of_injective
      (Subgroup.inclusion hKcommon) (Subgroup.inclusion_injective hKcommon)
    rwa [Subgroup.card_map_of_injective hc] at h
  have hcard : Nat.card other ≤ 2 * Nat.card K := by
    change Nat.card (VAt Γ (Γ.act conjugator third)) ≤ 2 * Nat.card K at hindex
    rw [← hotherMap, Subgroup.card_map_of_injective hc] at hindex
    exact hindex
  have hlength : 3 ≤ cp.length := by change 3 < cp.length at hb; omega
  let second := cp.path ⟨2, by omega⟩
  have hfirstAdj : Γ.adjacent second cp.firstStep := by
    have h := cp.path_adj ⟨1, by omega⟩
    change Γ.adjacent (cp.path ⟨1, by omega⟩) second at h
    rw [cp.path_first] at h
    exact Γ.adjacent_symm h
  have hthirdAdj : Γ.adjacent second third := by
    obtain ⟨index, hval, rfl⟩ := hthird
    have h := cp.path_adj ⟨2, by omega⟩
    have heq : (⟨2, by omega⟩ : Fin cp.length).succ = index := Fin.ext hval.symm
    exact heq ▸ h
  obtain ⟨mover, hmover⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity second
    ((mem_neighborhood_iff_adjacent Γ).mpr hfirstAdj)
    ((mem_neighborhood_iff_adjacent Γ).mpr hthirdAdj)
  have hcardEqual : Nat.card first = Nat.card other := by
    change Nat.card (v Γ cp.firstStep) = Nat.card (v Γ third)
    rw [← hmover, v_act, Subgroup.card_map_of_injective (MulAut.conj (mover : G)⁻¹).injective]
  have hproper : common < first := nine_six_intersection_lt ctx.toLocalContext third hthird
  have hnotOne : common.relIndex first ≠ 1 := by
    intro heq
    exact (not_le_of_gt hproper) (Subgroup.relIndex_eq_one.mp heq)
  have hproduct : common.relIndex first * Nat.card common = Nat.card first := by
    have h := (common.subgroupOf first).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h
    exact h
  have hpositive : 0 < Nat.card common := Nat.card_pos
  have hpositiveFirst : 0 < Nat.card first := Nat.card_pos
  have htwo : common.relIndex first = 2 := by
    have hle : common.relIndex first ≤ 2 := by
      nlinarith [hcardEqual.le.trans hcard]
    have hneZero : common.relIndex first ≠ 0 := by
      intro hzero
      rw [hzero, zero_mul] at hproduct
      omega
    omega
  have hindexFirst : QuotientCardEq first common 2 := by
    change Nat.card first = 2 * Nat.card common
    rw [htwo] at hproduct
    exact hproduct.symm
  have hbound := (lemma_nine_seven_ambient ctx (by omega) third hthird hindexFirst).1
  omega

/-- The original exact-index-two coatom obstruction. -/
public theorem nine_ten_predecessor_coatom_not_le_first
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (third : ctx.Γ.Vertex)
    (hthird : IsCriticalPathOffset ctx.Γ ctx.criticalPath 3 third)
    (conjugator : G) (hconjugator : conjugator ∈ GAt ctx.Γ ctx.criticalPath.firstStep)
    (K : Subgroup G)
    (hK : K ≤ VAt ctx.Γ (ctx.Γ.act conjugator third))
    (hindex : QuotientCardEq (VAt ctx.Γ (ctx.Γ.act conjugator third)) K 2) :
    ¬ K ≤ VAt ctx.Γ ctx.criticalPath.firstStep := by
  apply nine_ten_predecessor_large_subgroup_not_le_first ctx hb third hthird
    conjugator hconjugator K hK
  exact hindex.le

end Stellmacher.SectionNine
