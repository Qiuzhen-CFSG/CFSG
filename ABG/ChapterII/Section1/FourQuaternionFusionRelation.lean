module
public import ABG.ChapterII.Section1.CentricFusionRelation
public import ABG.ChapterII.Section1.CentricAutomorphisms
public import ABG.ChapterII.Section1.ExtremalNormalizerControl
/-!
# The exceptional normalizers for quasi-dihedral fusion

In ABG Chapter II §1 Proposition 1 (article pp.10–11), the only subgroups
that can introduce element fusion beyond conjugacy within the quasi-dihedral
Sylow two-subgroup are four groups and quaternion groups of order eight.
This module proves that reduction for any reflexive transitive relation
containing Sylow conjugacy. The exceptional local hypothesis concerns actual
ambient subgroups and their normalizer actions; it does not assume the four
fusion alternatives that the proposition must eventually establish.

Apply the centric extremal conjugation-family relation theorem. When the
subgroup automorphism group is a two-group, extremality realizes every
normalizer action inside the Sylow subgroup, so the step preserves the
relation. Otherwise the proved quasi-dihedral subgroup classification gives
a Klein four or quaternion-eight group. Transport that classification along
the actual subgroup inclusion equivalence and use the exceptional hypothesis.
-/

namespace ABG
open BenderSuzuki.External
/-- Ambient conjugacy preserves any Sylow-conjugacy relation preserved by
four and quaternion-eight extremal normalizer steps. -/
public theorem quasiDihedral_fusion_relation
    {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (hP : Stellmacher.IsSemidihedralGroup P)
    (R : P → P → Prop) (hrefl : ∀ x, R x x)
    (htrans : ∀ {x y z}, R x y → R y z → R x z)
    (hconj : ∀ {x y : P}, IsConj x y → R x y)
    (hlocal : ∀ (U : Subgroup G), HuppertExtremal P U →
      (IsKleinFour U ∨ Nonempty (U ≃* QuaternionGroup 2)) →
      ∀ g : G, g ∈ Subgroup.normalizer (U : Set G) →
      ∀ x y : P, (x : G) ∈ U → g⁻¹ * (x : G) * g = (y : G) → R x y)
    {x y : P} (hxy : IsConj (x : G) (y : G)) : R x y := by
  apply centric_fusion_relation P R hrefl htrans (fun U hU _ => ?_) hxy
  intro g hg x y hxU hstep
  by_cases hAut : IsPGroup 2 (MulAut U)
  · exact hconj (extremal_normalizer_fusion_control P U hU hAut g hg x y hxU hstep)
  · let X : Subgroup P := U.subgroupOf (P : Subgroup G)
    let e : X ≃* U := Subgroup.subgroupOfEquivOfLe hU.1
    have hXAut : ¬ IsPGroup 2 (MulAut X) := fun h => hAut (h.of_equiv (MulAut.congr e))
    have hsmall := QuasiDihedral.subgroup_automorphisms hP X hXAut
    apply hlocal U hU ?_ g hg x y hxU hstep
    rcases hsmall with hfour | hquaternion
    · exact Or.inl ⟨(Nat.card_congr e.toEquiv).symm.trans hfour.card_four,
        (Monoid.exponent_eq_of_mulEquiv e).symm.trans hfour.exponent_two⟩
    · obtain ⟨eQ⟩ := hquaternion
      exact Or.inr ⟨e.symm.trans eQ⟩
end ABG
