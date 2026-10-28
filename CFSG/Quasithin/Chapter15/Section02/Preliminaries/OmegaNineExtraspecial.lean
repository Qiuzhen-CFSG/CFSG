module

public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaStarSetup
public import Theory.GroupTheory.ExtraspecialCentralizerRank
public import Theory.Quasithin.CoprimeRank

/-!
# The centralizer in the extraspecial Omega branch

The literal star kernel C_M(V)* centralizes Y* by15.2.3(5). An actual
Heisenberg model of Y* supplies a noncentral cubic, giving a disjoint
commuting rank direction. Quasithinness bounds the kernel's three-rank
by one; its original preimage has the same three-rank through the normal
two-group kernel. The abelian order-nine action image identifies the
kernel on Y* with Z(Y*). Consequently every cubic in C_M(V)* is in Z(Y*).

The Heisenberg model is the genuine extraspecial branch witness produced
by the order-nine central-extension classification. The rank and cubic
containment are proved here from that witness, rather than assumed.

Source: Aschbacher--Smith15.2.3(1)(ii), printed pp.1104--1105.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The exact star action kernel centralizes the original residual's star image. -/
theorem source_omega_star_kernel_centralizes (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (imageRepresentation M V hV.normalized)) :
    (omegaStarActor hV.normalized ho).ker ≤ centralizer
      ((((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
        (QuotientGroup.mk' (pCore 2 M))) : Set (M ⧸ pCore 2 M)) := by
  rw [omegaStarActor_ker]
  exact le_centralizer_iff.mpr (le_sup_right.trans
    (source_omega_lemma_15_2_3_5 T hTM hu hV ho))

/-- On an extraspecial star residual, the literal action kernel is its center. -/
theorem source_omega_extraspecial_star_kernel (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hcard : Nat.card (((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
      (actionHom M V hV.normalized).rangeRestrict) = 9)
    (hex : IsExtraspecial 3 (((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
      (QuotientGroup.mk' (pCore 2 M)))) :
    let P := ((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
      (QuotientGroup.mk' (pCore 2 M))
    ((omegaStarActor hV.normalized ho).domRestrict P).ker = center P := by
  let P := ((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
    (QuotientGroup.mk' (pCore 2 M))
  let f := omegaStarActor hV.normalized ho
  let : IsExtraspecial 3 P := hex
  have hAb : IsMulCommutative (P.map f) := by
    apply IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3)
    rw [omegaStarActor_map]
    exact hcard
  have hder : ⁅P, P⁆ ≤ f.ker := by
    rw [← Subgroup.map_eq_bot_iff, map_commutator]
    exact commutator_self_eq_bot_iff.mpr hAb
  apply le_antisymm
  · intro x hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (source_omega_star_kernel_centralizes T hTM hu hV ho hx y y.property)
  · rw [← IsExtraspecial.commutator_eq_center (p := 3)]
    intro x hx
    apply hder
    rw [← P.map_subtype_commutator]
    exact mem_map_of_mem _ hx

/-- The star centralizer has three-rank at most one in the Heisenberg branch. -/
theorem source_omega_extraspecial_star_centralizer_rank
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (imageRepresentation M V hV.normalized))
    (he : Nonempty ((((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
      (QuotientGroup.mk' (pCore 2 M))) ≃* HeisenbergPrime 3)) :
    primeRank 3 (omegaStarActor hV.normalized ho).ker ≤ 1 := by
  obtain ⟨e⟩ := he
  apply primeRank_le_one_of_centralizes_heisenberg _ _
    (source_omega_star_kernel_centralizes T hM.2 hu hV ho) _ e
  rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 M) pCore_isPGroup]
  exact (hG.twoLocal_sqtk hM.1.1).stronglyQuasithin 3 Nat.prime_three (by decide)

/-- The original C_M(V), before quotienting, has three-rank at most one. -/
theorem source_omega_extraspecial_centralizer_rank
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (imageRepresentation M V hV.normalized))
    (he : Nonempty ((((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
      (QuotientGroup.mk' (pCore 2 M))) ≃* HeisenbergPrime 3)) :
    primeRank 3 (M ⊓ centralizer (V : Set G) : Subgroup G) ≤ 1 := by
  let C := (M ⊓ centralizer (V : Set G)).subgroupOf M
  let q := QuotientGroup.mk' (pCore 2 M)
  have hqk : IsPGroup 2 (q.subgroupMap C).ker := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  obtain ⟨k, hk⟩ := hqk.exists_card_eq
  have hcop : Nat.Coprime 3 (Nat.card (q.subgroupMap C).ker) := by
    rw [hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  have hr := source_omega_extraspecial_star_centralizer_rank hG T hM hu hV ho he
  rw [omegaStarActor_ker] at hr
  have heq := primeRank_eq_of_surjective_of_coprime 3 (q.subgroupMap C)
    (q.subgroupMap_surjective C) hcop
  have heq' := primeRank_equiv 3 (subgroupOfEquivOfLe
    (inf_le_left : M ⊓ centralizer (V : Set G) ≤ M))
  change primeRank 3 C = primeRank 3 (C.map q) at heq
  change primeRank 3 C = primeRank 3 (M ⊓ centralizer (V : Set G) : Subgroup G) at heq'
  exact heq'.symm.trans_le (heq.trans_le hr)

/-- Every cubic element of the star centralizer lies in the star residual center. -/
theorem source_omega_extraspecial_star_cubic_mem_center
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hcard : Nat.card (((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
      (actionHom M V hV.normalized).rangeRestrict) = 9)
    (he : Nonempty ((((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
      (QuotientGroup.mk' (pCore 2 M))) ≃* HeisenbergPrime 3))
    (x : M ⧸ pCore 2 M) (hx : x ∈ (omegaStarActor hV.normalized ho).ker)
    (hx3 : x ^ 3 = 1) :
    let P := ((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
      (QuotientGroup.mk' (pCore 2 M))
    x ∈ (center P).map P.subtype := by
  let Y := (caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M
  let P := Y.map (QuotientGroup.mk' (pCore 2 M))
  let : Y.Normal := source_omega_lemma_15_2_3_2 T hM.2 hV.normalized ho
  let : P.Normal := Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  obtain ⟨e⟩ := he
  let : IsExtraspecial 3 P := IsExtraspecial.of_mulEquiv e.symm
    (HeisenbergPrime.isExtraspecial (by decide))
  apply cubic_mem_extraspecial_center_of_primeRank_le_one P _
    (source_omega_extraspecial_star_centralizer_rank hG T hM hu hV ho ⟨e⟩) _ x hx hx3
  rintro _ ⟨z, hz, rfl⟩
  change z ∈ ((omegaStarActor hV.normalized ho).domRestrict P).ker
  rwa [source_omega_extraspecial_star_kernel T hM.2 hu hV ho hcard inferInstance]

end CFSG.Quasithin.Chapter15.Section02
