module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaNineStructure
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaFullNoncentral
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaCubicSylow

/-!
# The Omega centralizer rank bound and the original H-star obstruction

The cubic and order-nine branches of 15.2.3 both give three-rank at most
one for the original centralizer C_M(V). Passing through the two-core
quotient preserves this bound. For the literal X = O²(H ∩ M), the prepared
chosen module supplies X ≤ C_M(V) by 15.1.9(4). Thus X* cannot be elementary
of order nine, which is exactly the first exclusion in 15.2.4.

When V is the full local module, the earlier full-module core-growth proof
discharges noncentrality. For a proper chosen module that source premise
remains explicit. The separate E.2.2 argument producing X* ≃ E₉ from the
S₅ wreath C₂ model is not asserted here.

Source: Aschbacher--Smith, 15.2.3--4, printed pp.1104--1106.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The complete Omega row has centralizer three-rank at most one. -/
theorem source_omega_centralizer_rank
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hRc : ¬ (M ⊓ Mc).pCoreIn 2 ≤ centralizer (V : Set G)) :
    primeRank 3 (M ⊓ centralizer (V : Set G) : Subgroup G) ≤ 1 := by
  rcases source_omega_caseIIResidual_image_order T hM.2 hV.normalized ho hRc with h3 | h9
  · exact (source_omega_cubic_sylow_structure hG T hM hu hV ho h3).1
  · exact source_omega_nine_centralizer_rank hG T hM hu hV ho h9

/-- In the full-module branch, the source core argument supplies noncentrality. -/
theorem source_omega_full_centralizer_rank
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} [IsElementaryAbelian 2 (localModule T M)]
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M (localModule T M))
    (ho : SourceCases.Omega (imageRepresentation M (localModule T M) hV.normalized)) :
    primeRank 3 (M ⊓ centralizer (localModule T M : Set G) : Subgroup G) ≤ 1 := by
  exact source_omega_centralizer_rank hG T hM.1 hu hV ho
    (source_omega_full_core_noncentral hG T hempty hM hu hmany ho)

private theorem source_omega_star_centralizer_subgroup_rank
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V X : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hRc : ¬ (M ⊓ Mc).pCoreIn 2 ≤ centralizer (V : Set G))
    (hX : X ≤ M ⊓ centralizer (V : Set G)) :
    primeRank 3 ((X.subgroupOf M).map (QuotientGroup.mk' (pCore 2 M))) ≤ 1 := by
  let A := X.subgroupOf M
  let q := QuotientGroup.mk' (pCore 2 M)
  have hk : IsPGroup 2 (q.subgroupMap A).ker := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  obtain ⟨k, hk⟩ := hk.exists_card_eq
  have hcop : Nat.Coprime 3 (Nat.card (q.subgroupMap A).ker) := by
    rw [hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  have he := primeRank_eq_of_surjective_of_coprime 3 (q.subgroupMap A)
    (q.subgroupMap_surjective A) hcop
  have he' := primeRank_equiv 3 (subgroupOfEquivOfLe (hX.trans inf_le_left))
  have hbound := (Theory.GroupTheory.primeRank_le_of_injective 3 (Subgroup.inclusion hX)
    (Subgroup.inclusion_injective hX)).trans
      (source_omega_centralizer_rank hG T hM hu hV ho hRc)
  change primeRank 3 A = primeRank 3 (A.map q) at he
  change primeRank 3 A = primeRank 3 X at he'
  exact he.symm.trans_le (he'.trans_le hbound)

/-- The literal X* from the opening of 15.2.4 has three-rank at most one.
The prepared source module supplies X <= C_M(V) by 15.1.9(4). -/
theorem source_omega_HStar_intersection_star_rank
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V H : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hRc : ¬ (M ⊓ Mc).pCoreIn 2 ≤ centralizer (V : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    let X := (pResidual 2 (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype
    primeRank 3 ((X.subgroupOf M).map (QuotientGroup.mk' (pCore 2 M))) ≤ 1 := by
  exact source_omega_star_centralizer_subgroup_rank hG T hM hu hV ho hRc
    (le_inf ((map_subtype_le _).trans inf_le_right) (hV.intersection_residual H hH))

/-- The E9 star-image conclusion used in the opening of 15.2.4 excludes
case (3) of 15.2.1, with the original H-star intersection and quotient map. -/
theorem source_omega_HStar_not_elementary_nine
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V H : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hRc : ¬ (M ⊓ Mc).pCoreIn 2 ≤ centralizer (V : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    let X := (pResidual 2 (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype
    let A := (X.subgroupOf M).map (QuotientGroup.mk' (pCore 2 M))
    ¬ (IsElementaryAbelian 3 A ∧ Nat.card A = 9) := by
  let X := (pResidual 2 (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype
  let A := (X.subgroupOf M).map (QuotientGroup.mk' (pCore 2 M))
  change ¬ (IsElementaryAbelian 3 A ∧ Nat.card A = 9)
  rintro ⟨helem, hc⟩
  let : IsElementaryAbelian 3 A := helem
  have hr : primeRank 3 A ≤ 1 := source_omega_HStar_intersection_star_rank hG T hM hu hV ho hRc hH
  have htop : IsElementaryAbelian 3 (⊤ : Subgroup A) :=
    IsElementaryAbelian.of_injective (⊤ : Subgroup A).subtype (⊤ : Subgroup A).subtype_injective
  have hb := (primeRank_le_iff_elementary_card_le A).mp hr ⊤ htop
  have he : Nat.card (⊤ : Subgroup A) = Nat.card A := Nat.card_congr Subgroup.topEquiv.toEquiv
  rw [he] at hb
  change Nat.card A = 9 at hc
  norm_num [hc] at hb

/-- The full-module 15.2.4 application has no retained intersection-core
noncentrality or residual-centralization premise. -/
theorem source_omega_full_HStar_not_elementary_nine
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc H : Subgroup G} [IsElementaryAbelian 2 (localModule T M)]
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M (localModule T M))
    (ho : SourceCases.Omega (imageRepresentation M (localModule T M) hV.normalized))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    let X := (pResidual 2 (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype
    let A := (X.subgroupOf M).map (QuotientGroup.mk' (pCore 2 M))
    ¬ (IsElementaryAbelian 3 A ∧ Nat.card A = 9) := by
  exact source_omega_HStar_not_elementary_nine hG T hM.1 hu hV ho
    (source_omega_full_core_noncentral hG T hempty hM hu hmany ho) hH

end CFSG.Quasithin.Chapter15.Section02
