module
public import ABG.ChapterII.Section1.FocalGenerators
public import Theory.GroupTheory.NormalizerFusionIndexControl
/-!
# No new fusion at outer automizer index two

A four subgroup or quaternion subgroup of order eight inside a
quasi-dihedral subgroup has internal normalizer index two, and its internal
centralizer is contained in it. If its ambient outer automizer index is also
two, every normalizer step is therefore conjugacy inside the quasi-dihedral
subgroup. In particular all its local fusion differences lie in the derived
subgroup. No Sylow or extremality hypothesis is required for this local fact.

Transport the subgroup type through the actual inclusion equivalence and
apply Lemma II.1.1(ii) to obtain the internal centralizer and normalizer
calculations. Centralizer containment restricts the outer denominator
`U C_G(U)` to `U`. The generic equality-of-indices theorem then realizes
normalizer fusion internally. The final corollary writes the resulting
difference as a commutator.

This supplies the low-index local cases of ABG Chapter II §1 Proposition 1,
article pp.10–11. The four-subgroup ordinary automizer index agrees with its
outer index because the subgroup is abelian; the quaternion denominator
retains the essential factor `U`.
-/

namespace ABG.QuasiDihedral
/-- An exceptional small subgroup with outer index two introduces no new ambient fusion. -/
public theorem small_normalizer_fusion_control
    {G : Type*} [Group G] [Finite G] (P U : Subgroup G)
    (hP : Stellmacher.IsSemidihedralGroup P) (hUP : U ≤ P)
    (hsmall : IsKleinFour U ∨ Nonempty (U ≃* QuaternionGroup 2))
    (houter : ABG.outerAutomizerIndex U = 2)
    (g : G) (hg : g ∈ Subgroup.normalizer (U : Set G))
    (x y : P) (hxU : (x : G) ∈ U)
    (hxy : g⁻¹ * (x : G) * g = (y : G)) : IsConj x y := by
  let X := U.subgroupOf P
  let e := Subgroup.subgroupOfEquivOfLe hUP
  have hX : IsKleinFour X ∨ Nonempty (X ≃* QuaternionGroup 2) := by
    rcases hsmall with hfour | hquaternion
    · exact Or.inl ⟨(Nat.card_congr e.toEquiv).trans hfour.card_four,
        (Monoid.exponent_eq_of_mulEquiv e).trans hfour.exponent_two⟩
    · obtain ⟨eQ⟩ := hquaternion
      exact Or.inr ⟨e.trans eQ⟩
  obtain ⟨_, _, _, _, _, _, hlocal⟩ := four_quaternion_subgroups hP
  obtain ⟨hC, hN⟩ := hlocal X hX
  have hCP : (Subgroup.centralizer (U : Set G)).subgroupOf P ≤ X := by
    intro z hz
    have hzC : z ∈ Subgroup.centralizer (X : Set P) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hz t ht)
    rw [hC] at hzC
    exact Subgroup.map_subtype_le _ hzC
  apply Subgroup.normalizer_fusion_control_of_outer_index_eq P U hUP ?_ g hg x y hxU hxy
  rw [Subgroup.sup_centralizer_subgroupOf_eq_of_centralizer_le P U hUP hCP,
    Subgroup.subgroupOf_normalizer_eq hUP]
  exact hN.trans houter.symm

/-- Low-index normalizer fusion contributes only Sylow commutators to the focal subgroup. -/
public theorem normalizerFusionSubgroup_le_commutator_of_outer_index_two
    {G : Type*} [Group G] [Finite G] (P U : Subgroup G)
    (hP : Stellmacher.IsSemidihedralGroup P) (hUP : U ≤ P)
    (hsmall : IsKleinFour U ∨ Nonempty (U ≃* QuaternionGroup 2))
    (houter : ABG.outerAutomizerIndex U = 2) :
    ABG.normalizerFusionSubgroup P U ≤ commutator P := by
  rw [ABG.normalizerFusionSubgroup, Subgroup.closure_le]
  rintro z ⟨x, y, g, hg, hx, hxy, rfl⟩
  obtain ⟨s, rfl⟩ := isConj_iff.mp (small_normalizer_fusion_control P U hP hUP hsmall houter
    g hg x y hx hxy)
  have h := Subgroup.commutator_mem_commutator (Subgroup.mem_top x⁻¹) (Subgroup.mem_top s)
  simpa only [SetLike.mem_coe, commutator_def, commutatorElement_def, inv_inv, mul_assoc] using h
end ABG.QuasiDihedral
