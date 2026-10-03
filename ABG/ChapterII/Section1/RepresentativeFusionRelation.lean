module
public import ABG.ChapterII.Section1.FourQuaternionFusionRelation
public import ABG.ChapterII.Section1.SmallSubgroupConjugacy
public import ABG.ChapterII.Section1.FusionPatterns
public import Theory.GroupTheory.FusionRelationTransport
/-!
# Fusion controlled by the two chosen representatives

For a finite group with a quasi-dihedral Sylow two-subgroup, a reflexive
transitive relation containing conjugacy within the Sylow subgroup is
preserved by all ambient conjugacies if it is preserved by normalizer steps
at the chosen four subgroup and quaternion subgroup of order eight.
The chosen subgroups are exactly those of `QuasiDihedralFusionFrame`; no
extremality assumption on these representatives is imposed.

The exceptional-family fusion theorem reduces to a four or quaternion-eight
extremal subgroup. Lemma II.1.1(ii), transported to ambient subgroups, makes
it conjugate inside the Sylow subgroup to the chosen representative of the
same type. Conjugate the whole normalizer step and compose the endpoint
Sylow conjugacies to apply the representative hypothesis.

This supplies the control reduction for ABG Chapter II §1 Proposition 1,
article pp.10–11 of `refs/latex/alperin-brauer-gorenstein.tex`. The separate
normalizer-action and focal calculations will turn this relation principle
into the four complete source fusion patterns.
-/

namespace ABG
/-- The chosen four and quaternion-eight normalizers control relations under ambient fusion. -/
public theorem quasiDihedral_representative_fusion_relation
    {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (T Q : Subgroup G) (hframe : QuasiDihedralFusionFrame P T Q)
    (R : P → P → Prop) (hrefl : ∀ x, R x x)
    (htrans : ∀ {x y z}, R x y → R y z → R x z)
    (hconj : ∀ {x y : P}, IsConj x y → R x y)
    (hT : ∀ g : G, g ∈ Subgroup.normalizer (T : Set G) →
      ∀ x y : P, (x : G) ∈ T → g⁻¹ * (x : G) * g = (y : G) → R x y)
    (hQ : ∀ g : G, g ∈ Subgroup.normalizer (Q : Set G) →
      ∀ x y : P, (x : G) ∈ Q → g⁻¹ * (x : G) * g = (y : G) → R x y)
    {x y : P} (hxy : IsConj (x : G) (y : G)) : R x y := by
  obtain ⟨hP, hTP, hQP, hfour, hquaternion⟩ := hframe
  apply quasiDihedral_fusion_relation P hP R hrefl htrans hconj (fun U hU hsmall => ?_) hxy
  rcases hsmall with hsmall | hsmall
  · obtain ⟨s, hs⟩ := QuasiDihedral.four_subgroup_ambient_conjugacy
      (P : Subgroup G) U T hP hU.1 hTP hsmall hfour
    exact Subgroup.normalizer_fusion_relation_of_conjugate (P : Subgroup G) U T R
      htrans hconj s hs hT
  · obtain ⟨s, hs⟩ := QuasiDihedral.quaternion_subgroup_ambient_conjugacy
      (P : Subgroup G) U Q hP hU.1 hQP hsmall hquaternion
    exact Subgroup.normalizer_fusion_relation_of_conjugate (P : Subgroup G) U Q R
      htrans hconj s hs hQ
end ABG
