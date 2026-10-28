module
public import Stellmacher.SectionNine.NineEightContainedCenterPathIndex
public import Stellmacher.SectionNine.LemmaNineSeven

/-!
# The preceding module intersection has index at least four

At critical distance greater than three, the module at any preceding neighbor
other than the first vertex meets the first module with index at least four.
This supplies source (9.9)(2) from the proved numbered (9.7).

The module is elementary abelian, so the intersection index is a power of
two. Index one contradicts the distinct-neighbor-module theorem. At index
two, cubic two-arc transitivity sends the two neighboring vertices to offsets
one and three on the actual critical path. The same conjugation carries both
module factors, preserving their intersection and cardinalities. The actual
ambient (9.7) theorem then forces critical length three, a contradiction.

Source: Stellmacher (9.9)(2), printed p.56/PDF p.46 of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_nine_previous_intersection_index_ge_four
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (previous : ctx.Γ.Vertex)
    (hprevious : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hne : previous ≠ ctx.criticalPath.firstStep) :
    4 * Nat.card (VAt ctx.Γ previous ⊓ VAt ctx.Γ ctx.criticalPath.firstStep : Subgroup G)
      ≤ Nat.card (VAt ctx.Γ previous) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let U := VAt Γ previous
  let I := U⊓VAt Γ cp.firstStep
  have hlong : 1<cp.length := by change 3<cp.length at hb; omega
  obtain ⟨aligner0,halign0⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.a
    ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj) hprevious
  have hcardEq : Nat.card U=Nat.card (VAt Γ cp.firstStep) := by
    change Nat.card (v Γ previous)=Nat.card (v Γ cp.firstStep)
    rw [← halign0,v_act,Subgroup.card_map_of_injective (MulAut.conj (aligner0:G)⁻¹).injective]
  have hp : IsPGroup 2 U := by
    change IsPGroup 2 (v Γ previous)
    rw [← halign0,v_act]
    let _ := ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hlong).1
    exact (IsElementaryAbelian.isPGroup 2 (v Γ cp.firstStep)).map _
  have hcount := (I.subgroupOf U).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show I≤U from inf_le_left)).toEquiv] at hcount
  change I.relIndex U*Nat.card I=Nat.card U at hcount
  obtain ⟨k,hk⟩ := hp.index (I.subgroupOf U)
  change I.relIndex U=2^k at hk
  have hneOne : I.relIndex U≠1 := by
    intro hindex
    have hle : U≤VAt Γ cp.firstStep := (Subgroup.relIndex_eq_one.mp hindex).trans inf_le_right
    exact nine_eight_distinct_neighbor_modules ctx hlong previous hprevious hne
      (Subgroup.eq_of_le_of_card_ge hle hcardEq.ge)
  have hneTwo : I.relIndex U≠2 := by
    intro hindex
    have hbackward : QuotientCardEq U I 2 := by
      change Nat.card U=2*Nat.card I
      rw [hindex] at hcount
      exact hcount.symm
    have hb' : 3 < cp.length := hb
    let second := cp.path ⟨2, by omega⟩
    let third := cp.path ⟨3, by omega⟩
    have hleft : Γ.adjacent second cp.firstStep := by
      have hedge := cp.path_adj ⟨1, by omega⟩
      change Γ.adjacent (cp.path ⟨1, by omega⟩) second at hedge
      rw [cp.path_first] at hedge
      exact Γ.adjacent_symm hedge
    have hright : Γ.adjacent second third := cp.path_adj ⟨2, by omega⟩
    have hdistinct : cp.firstStep ≠ third := by
      have hh := nine_seven_path_vertices_ne Γ cp 1 3 (by omega) (by omega)
      rwa [cp.path_first] at hh
    obtain ⟨aligner, haligner⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.firstStep
      ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj))
      ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hleft))
    have horbit : IsConjugateVertex Γ cp.a second := ⟨aligner, haligner⟩
    obtain ⟨mover, hmovePrevious, _, hmoveFirst⟩ := nine_seven_two_arc_transport ctx.sectionSeven Γ
      ((mem_neighborhood_iff_adjacent Γ).mp hprevious) cp.firstStep_adj hne hleft hright hdistinct horbit
      (lemma_nine_three_ambient ctx hlong second horbit).1
    have hcardPrevious : Nat.card (VAt Γ previous) = Nat.card (VAt Γ cp.firstStep) := by
      change Nat.card (v Γ previous) = Nat.card (v Γ cp.firstStep)
      rw [← hmovePrevious, v_act]
      exact (Subgroup.card_map_of_injective (MulAut.conj mover⁻¹).injective).symm
    have hmap : (VAt Γ previous ⊓ VAt Γ cp.firstStep).map (MulAut.conj mover⁻¹).toMonoidHom =
        VAt Γ cp.firstStep ⊓ VAt Γ third := by
      rw [Subgroup.map_inf _ _ _ (MulAut.conj mover⁻¹).injective]
      change (v Γ previous).map _ ⊓ (v Γ cp.firstStep).map _ = _
      rw [← v_act, ← v_act, hmovePrevious, hmoveFirst]
    have hcardIntersection : Nat.card (VAt Γ previous ⊓ VAt Γ cp.firstStep : Subgroup G) =
        Nat.card (VAt Γ cp.firstStep ⊓ VAt Γ third : Subgroup G) := by
      rw [← hmap]
      exact (Subgroup.card_map_of_injective (MulAut.conj mover⁻¹).injective).symm
    have hpathIndex : QuotientCardEq (VAt Γ cp.firstStep)
        (VAt Γ cp.firstStep⊓VAt Γ third) 2 := by
      change Nat.card U=2*Nat.card I at hbackward
      change Nat.card (VAt Γ cp.firstStep)=2*Nat.card (VAt Γ cp.firstStep⊓VAt Γ third : Subgroup G)
      change Nat.card (VAt Γ previous)=2*Nat.card (VAt Γ previous⊓VAt Γ cp.firstStep : Subgroup G) at hbackward
      rwa [hcardPrevious,hcardIntersection] at hbackward
    have hthree := (lemma_nine_seven_ambient ctx hlong third
      ⟨⟨3,by omega⟩,rfl,rfl⟩ hpathIndex).1
    omega
  have hk2 : 2≤k := by
    by_contra hnot
    have hsmall : k=0∨k=1 := by omega
    rcases hsmall with rfl|rfl
    · exact hneOne (by simpa using hk)
    · exact hneTwo (by simpa using hk)
  have hfour : 4≤I.relIndex U := by
    rw [hk]
    exact Nat.pow_le_pow_right (n:=2) (by decide) hk2
  change 4*Nat.card I≤Nat.card U
  rw [← hcount]
  exact Nat.mul_le_mul_right _ hfour

end Stellmacher.SectionNine
