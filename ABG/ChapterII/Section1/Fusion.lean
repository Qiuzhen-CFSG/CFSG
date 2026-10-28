module
public import ABG.ChapterII.Section1.FocalCases
public import ABG.ChapterII.Section1.InvolutionFusion
public import ABG.ChapterII.Section1.OrderFourFusion
public import ABG.ChapterII.Section1.FourAutomizerIndex
public import ABG.ChapterII.Section1.QuaternionAutomizerIndex
public import ABG.ChapterII.Section1.FocalIndexTwo
public import ABG.ChapterII.Section1.CyclicFocalComplement
public import ABG.ChapterII.Section1.FocalFull
/-!
# ABG Chapter II, Section 1, Proposition 1

A finite group with a quasi-dihedral Sylow two-subgroup has exactly the
four source alternatives for fusion. The theorem retains the chosen four
subgroup T and quaternion subgroup Q: both automizer indices, the complete
involution and order-four class counts, the normal-subgroup and normal
complement conclusions, and the Q-case weak closure of the Sylow center
are all asserted by the production fusion-pattern predicates.

The two automizer indices are each two or six. The focal calculations give
respectively the cyclic derived subgroup, its generalized quaternion or
dihedral maximal join, or the whole Sylow subgroup. An index-two focal
subgroup is realized by an actual transfer kernel, including an actual
Sylow subgroup of that kernel and absence of further normal index-two
subgroups. Cyclic focal subgroup gives a normal two-complement. Full focal
subgroup rules out ambient normal index two by the focal subgroup theorem.
The independently proved global class counts and center weak closure supply
the remaining clauses in each case.

This is the complete Proposition 1 on article pp.10–11 of
`refs/latex/alperin-brauer-gorenstein.tex`, following the paper's proposed
Alperin/focal approach. It applies to arbitrary finite ambient groups and
does not assume simplicity or any of the four conclusions.
-/

namespace ABG
/-- All four complete quasi-dihedral fusion alternatives of ABG II.1 Proposition 1. -/
public theorem quasiDihedral_fusion
    {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (T Q : Subgroup G) (hframe : QuasiDihedralFusionFrame P T Q) :
    QuasiDihedralQDPattern T Q ∨ QuasiDihedralQPattern P T Q ∨
      QuasiDihedralDPattern T Q ∨ QuasiDihedralNormalComplementPattern T Q := by
  have hF := quasiDihedral_focal_subgroup_cases P T Q hframe
  have hI := quasiDihedral_involution_fusion P T Q hframe
  have hO := quasiDihedral_order_four_fusion P T Q hframe
  obtain ⟨hP, hTP, hQP, hT, hQ⟩ := hframe
  have hTPfour : IsKleinFour (T.subgroupOf (P : Subgroup G)) := by
    let e := Subgroup.subgroupOfEquivOfLe hTP
    exact ⟨(Nat.card_congr e.toEquiv).trans hT.card_four,
      (Monoid.exponent_eq_of_mulEquiv e).trans hT.exponent_two⟩
  have hQPquaternion : Nonempty ((Q.subgroupOf (P : Subgroup G)) ≃* QuaternionGroup 2) := by
    obtain ⟨eQ⟩ := hQ
    exact ⟨(Subgroup.subgroupOfEquivOfLe hQP).trans eQ⟩
  obtain ⟨hDi, hDmodel, hQi, hQmodel, _, _, hcyclic⟩ := QuasiDihedral.frattini_joins hP
    (T.subgroupOf (P : Subgroup G)) (Q.subgroupOf (P : Subgroup G)) hTPfour hQPquaternion
  rcases QuasiDihedral.four_automizer_index P hP T hTP hT with hT2 | hT6 <;>
    rcases QuasiDihedral.quaternion_outer_automizer_index P hP Q hQP hQ with hQ2 | hQ6
  · apply Or.inr (Or.inr (Or.inr ?_))
    have hcomp : HasNormalPComplement 2 G :=
      hasNormalTwoComplement_of_cyclic_focalSubgroupOf P (by
        rw [hF.1 hT2 hQ2]
        exact hcyclic)
    exact ⟨hcomp, (hI.2 hT2).1, hO.2 hQ2, hT2, hQ2⟩
  · apply Or.inr (Or.inl ?_)
    obtain ⟨K, hK, hKi, hKno, R, _, hR⟩ :=
      exists_normal_index_two_sylow_of_focalSubgroupOf P
        (commutator P ⊔ Q.subgroupOf (P : Subgroup G)) hQi (hF.2.1 hT2 hQ6)
    obtain ⟨eR⟩ := hR
    obtain ⟨n, hn, hmodel⟩ := hQmodel
    obtain ⟨eF⟩ := hmodel
    have hSylow : HasGeneralizedQuaternionSylowTwo K := ⟨R, n, hn, ⟨eR.trans eF⟩⟩
    exact ⟨⟨K, hK, hKi, hSylow, hKno⟩, (hI.2 hT2).2, (hI.2 hT2).1,
      hO.1 hQ6, hT2, hQ6⟩
  · apply Or.inr (Or.inr (Or.inl ?_))
    obtain ⟨K, hK, hKi, hKno, R, _, hR⟩ :=
      exists_normal_index_two_sylow_of_focalSubgroupOf P
        (commutator P ⊔ T.subgroupOf (P : Subgroup G)) hDi (hF.2.2.1 hT6 hQ2)
    obtain ⟨eR⟩ := hR
    obtain ⟨n, hmodel⟩ := hDmodel
    obtain ⟨eF⟩ := hmodel
    have hSylow : HasDihedralSylowTwo K := ⟨R, n, ⟨eR.trans eF⟩⟩
    exact ⟨⟨K, hK, hKi, hSylow, hKno⟩, hI.1 hT6, hO.2 hQ2, hT6, hQ2⟩
  · exact Or.inl ⟨no_normal_index_two_of_focal_top P (hF.2.2.2 hT6 hQ6),
      hI.1 hT6, hO.1 hQ6, hT6, hQ6⟩
end ABG
