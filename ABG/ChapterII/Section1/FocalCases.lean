module
public import ABG.ChapterII.Section1.FocalGenerators
public import ABG.ChapterII.Section1.FourNormalizerFusion
public import ABG.ChapterII.Section1.QuaternionNormalizerFusion
public import ABG.ChapterII.Section1.SmallNormalizerFusionControl
public import ABG.ChapterII.Section1.FrattiniJoins
/-!
# The four quasi-dihedral focal subgroups

For the fixed four subgroup T and quaternion subgroup Q in a quasi-dihedral
Sylow two-subgroup P, the ordinary automizer index of T and outer automizer
index of Q determine the focal subgroup. The pairs (2,2), (2,6), (6,2),
and (6,6) give respectively the derived subgroup, its join with Q, its
join with T, and the whole Sylow subgroup. All joins use the actual
subgroup inclusions into P; the quaternion denominator retains Q C_G(Q).

The general focal-generator theorem reduces the calculation to the two
local actions. Index two contributes only derived-subgroup elements;
index six contributes the entire corresponding small subgroup. Lattice
absorption proves the first three equalities. The previously identified
Frattini joins generate P when both actions are full, giving the fourth.
The four group's ordinary and outer indices agree because it is abelian.

These are the focal calculations underlying all four alternatives of
Alperin–Brauer–Gorenstein Chapter II §1 Proposition 1, article pp.10–11.
The normal-subgroup and global class-count consequences are assembled
separately from these exact subgroup equalities.
-/

namespace ABG
/-- All four exact focal subgroup values for the chosen source fusion frame. -/
public theorem quasiDihedral_focal_subgroup_cases
    {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (T Q : Subgroup G) (hframe : QuasiDihedralFusionFrame P T Q) :
    (automizerIndex T = 2 → outerAutomizerIndex Q = 2 →
      (P : Subgroup G).focalSubgroupOf = commutator P) ∧
    (automizerIndex T = 2 → outerAutomizerIndex Q = 6 →
      (P : Subgroup G).focalSubgroupOf = commutator P ⊔ Q.subgroupOf (P : Subgroup G)) ∧
    (automizerIndex T = 6 → outerAutomizerIndex Q = 2 →
      (P : Subgroup G).focalSubgroupOf = commutator P ⊔ T.subgroupOf (P : Subgroup G)) ∧
    (automizerIndex T = 6 → outerAutomizerIndex Q = 6 →
      (P : Subgroup G).focalSubgroupOf = ⊤) := by
  have hF := quasiDihedral_focalSubgroupOf_eq P T Q hframe
  obtain ⟨hP, hTP, hQP, hT, hQ⟩ := hframe
  let : IsKleinFour T := hT
  let : IsMulCommutative T := IsKleinFour.isMulCommutative
  have hTout : outerAutomizerIndex T = automizerIndex T := by
    unfold outerAutomizerIndex automizerIndex
    rw [sup_eq_right.mpr (Subgroup.le_centralizer (H := T))]
  have hTlow (h : automizerIndex T = 2) :
      normalizerFusionSubgroup (P : Subgroup G) T ≤ commutator P :=
    QuasiDihedral.normalizerFusionSubgroup_le_commutator_of_outer_index_two
      (P : Subgroup G) T hP hTP (Or.inl hT) (hTout.trans h)
  have hQlow (h : outerAutomizerIndex Q = 2) :
      normalizerFusionSubgroup (P : Subgroup G) Q ≤ commutator P :=
    QuasiDihedral.normalizerFusionSubgroup_le_commutator_of_outer_index_two
      (P : Subgroup G) Q hP hQP (Or.inr hQ) h
  have hThigh := four_normalizerFusionSubgroup_eq (P : Subgroup G) T hTP hT
  have hQhigh := quaternion_normalizerFusionSubgroup_eq (P : Subgroup G) Q hQP hQ
  have hTPfour : IsKleinFour (T.subgroupOf (P : Subgroup G)) := by
    let e := Subgroup.subgroupOfEquivOfLe hTP
    exact ⟨(Nat.card_congr e.toEquiv).trans hT.card_four,
      (Monoid.exponent_eq_of_mulEquiv e).trans hT.exponent_two⟩
  have hQPquaternion : Nonempty ((Q.subgroupOf (P : Subgroup G)) ≃* QuaternionGroup 2) := by
    obtain ⟨eQ⟩ := hQ
    exact ⟨(Subgroup.subgroupOfEquivOfLe hQP).trans eQ⟩
  have hjoins := QuasiDihedral.frattini_joins hP
    (T.subgroupOf (P : Subgroup G)) (Q.subgroupOf (P : Subgroup G)) hTPfour hQPquaternion
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hT2 hQ2
    rw [hF, sup_eq_left.mpr (hTlow hT2), sup_eq_left.mpr (hQlow hQ2)]
  · intro hT2 hQ6
    rw [hF, sup_eq_left.mpr (hTlow hT2), hQhigh hQ6]
  · intro hT6 hQ2
    rw [hF, hThigh hT6, sup_eq_left.mpr ((hQlow hQ2).trans le_sup_left)]
  · intro hT6 hQ6
    rw [hF, hThigh hT6, hQhigh hQ6]
    exact hjoins.2.2.2.2.1
end ABG
