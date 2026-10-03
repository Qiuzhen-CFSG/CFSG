module
public import ABG.ChapterII.Section1.LargeCyclicIntersection
public import Theory.GroupTheory.CyclicTwoAut
public import Theory.GroupTheory.CharacteristicIndexTwoAut
public import ABG.ChapterII.Section1.SmallSubgroupModels
public import GorensteinWalter.DihedralAut
/-!
# Subgroups with exceptional automorphisms

A subgroup of a quasi-dihedral group whose automorphism group is not a
two-group is a Klein four group or the quaternion group of order eight.
The centric case supplies the local family for the fusion proof of ABG
Chapter II, Section 1, Proposition 1 (article pages 10–11 of
`refs/latex/alperin-brauer-gorenstein.tex`). This is the quasi-dihedral
counterpart of the explicitly stated wreathed criterion in Lemma 3.

Intersect the subgroup with the cyclic maximal subgroup of the ambient
presentation. If the subgroup is cyclic, its automorphism group is already
a two-group. Otherwise the intersection has index two. An intersection
of order at least eight is characteristic, since every element outside it
has order at most four. Restriction of automorphisms then forces the full
automorphism group to be a two-group. Thus any exception has order at most
eight. The explicit small-subgroup models leave cyclic, Klein four,
dihedral-eight and quaternion-eight possibilities; cyclic and dihedral
automorphism groups are two-groups, eliminating those alternatives.

The argument does not need self-centralization, so the reusable subgroup
theorem is given first. The requested centric interface is retained as a
corollary with its full hypothesis, for direct use by the fusion reduction.
All group models, intersection subgroups, and automorphisms are the actual
ones from the production presentation, not classification assumptions.
-/

namespace ABG.QuasiDihedral
variable {G : Type*} [Group G]

private theorem card_le_eight_of_not_aut_two (hG : Stellmacher.IsSemidihedralGroup G)
    (X : Subgroup G) (hAut : ¬ IsPGroup 2 (MulAut X)) : Nat.card X ≤ 8 := by
  obtain ⟨n, hn, hcard, a, b, ha, hb, hab, hgen⟩ := hG
  let : Finite G := Nat.finite_of_card_ne_zero (hcard ▸ by positivity)
  have hXp : IsPGroup 2 X := (IsPGroup.of_card hcard).to_subgroup X
  have hX : ¬ X ≤ Subgroup.zpowers a := by
    intro hle
    let : IsCyclic X := Subgroup.isCyclic_of_le hle
    exact hAut (hXp.mulAut_of_isCyclic_two)
  let A := (Subgroup.zpowers a).subgroupOf X
  have hAi : A.index = 2 := cyclic_intersection_index_two hn hcard a b ha hb hab hgen X hX
  have hAp : IsPGroup 2 A := hXp.to_subgroup A
  let f : A →* Subgroup.zpowers a :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : Subgroup.zpowers a => z.val) h))
  let : IsCyclic A := isCyclic_of_injective f hf
  have hnotlarge : ¬ 8 ≤ Nat.card A := by
    intro hlarge
    let : A.Characteristic := large_cyclic_intersection_characteristic hn a b ha hb hab hgen X hlarge
    exact hAut (Subgroup.isPGroup_mulAut_of_characteristic_index_two A hAi hAp
      hAp.mulAut_of_isCyclic_two)
  obtain ⟨k, hk⟩ := hAp.exists_card_eq
  have hklt : k < 3 := by
    by_contra h
    have hp : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    exact hnotlarge (by rw [hk]; exact hp)
  have hAc : Nat.card A ≤ 4 := by
    rw [hk]
    exact Nat.pow_le_pow_right (by decide) (by omega : k ≤ 2)
  have hmul := A.card_mul_index
  rw [hAi] at hmul
  omega
/-- Only Klein-four and quaternion-eight subgroups can have an automorphism group that is not a two-group. -/
public theorem subgroup_automorphisms (hG : Stellmacher.IsSemidihedralGroup G)
    (X : Subgroup G)
    (hAut : ¬ IsPGroup 2 (MulAut X)) :
    IsKleinFour X ∨ Nonempty (X ≃* QuaternionGroup 2) := by
  have hsmall := small_subgroup_models hG X (card_le_eight_of_not_aut_two hG X hAut)
  obtain ⟨n, _, hcard, _⟩ := hG
  let : Finite G := Nat.finite_of_card_ne_zero (hcard ▸ by positivity)
  have hXp : IsPGroup 2 X := (IsPGroup.of_card hcard).to_subgroup X
  rcases hsmall with hcyclic | hfour | hdihedral | hquaternion
  · let := hcyclic
    exact (hAut hXp.mulAut_of_isCyclic_two).elim
  · exact Or.inl hfour
  · obtain ⟨e⟩ := hdihedral
    have hD : IsPGroup 2 (MulAut (DihedralGroup 4)) :=
      GorensteinWalter.dihedral_mulAut_is_twoGroup (m := 2) (by decide)
    exact (hAut (hD.of_equiv (MulAut.congr e).symm)).elim
  · exact Or.inr hquaternion
/-- The exceptional centric subgroups used in the quasi-dihedral fusion reduction. -/
public theorem centric_automorphisms (hG : Stellmacher.IsSemidihedralGroup G)
    (X : Subgroup G) (_hcentric : Subgroup.centralizer (X : Set G) ≤ X)
    (hAut : ¬ IsPGroup 2 (MulAut X)) :
    IsKleinFour X ∨ Nonempty (X ≃* QuaternionGroup 2) :=
  subgroup_automorphisms hG X hAut
end ABG.QuasiDihedral
