module

public import Theory.GroupTheory.PGroup.NormalFour
public import Theory.GroupTheory.PGroup.CharacteristicTwoNormalClosure
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators
public import Theory.GroupTheory.NormalCenterQuotient
public import Theory.GroupTheory.Fitting.Centralizer

/-!
# Four-groups in a self-centralizing two-core

If the two-core of a finite group is self-centralizing and a Sylow two-subgroup
contains an elementary eight, the two-core contains an elementary four.
Consequently this holds in a solvable group with trivial odd core. A four-group
normalized by the two-core and containing an ambient central involution must
itself lie in the two-core: otherwise its commutators with the core are central,
and the same normal-closure argument supplies the containment.

Choose a normal four-group in the Sylow subgroup. If the two-core has no four,
its central involution is its unique involution, so its first omega subgroup
is characteristic of order two and hence central in the whole group. The
commutator of the two-core with the normal four lies in this omega subgroup.
The characteristic-two normal-closure lemma then puts the four in the two-core,
a contradiction. This avoids cyclic/quaternion classification.

This is the Fitting-theoretic step in solvable two-generated-core arguments;
compare GLS, Number 2, Section 22, and Kurzweil--Stellmacher, 8.3.4.
-/

open Subgroup

private theorem omega_card_two_of_no_four
    {R : Type*} [Group R] [Finite R] [Nontrivial R] (hR : IsPGroup 2 R)
    (hfour : ∀ V : Subgroup R, IsElementaryAbelian 2 V → Nat.card V ≠ 4) :
    Nat.card (omega₁ R (p := 2)) = 2 := by
  let : Nontrivial (center R) := hR.center_nontrivial
  have hdiv : 2 ∣ Nat.card (center R) := by
    rcases (hR.to_subgroup (center R)).card_eq_or_dvd with h | h
    · exact (ne_of_gt hR.bot_lt_center (Subgroup.card_eq_one.mp h)).elim
    · exact h
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center R) 2 hdiv
  have hzord : orderOf (z : R) = 2 := (Subgroup.orderOf_coe z).trans hz
  have hzpow : (z : R) ^ 2 = 1 := by rw [← hzord]; exact pow_orderOf_eq_one _
  have huniq : ∀ x : R, x ^ 2 = 1 → x = 1 ∨ x = z := by
    intro x hx
    by_cases hxone : x = 1
    · exact Or.inl hxone
    right
    by_contra hxz
    have hxord : orderOf x = 2 := orderOf_eq_prime hx hxone
    let V := closure ({x, (z : R)} : Set R)
    let : IsKleinFour V := isKleinFour_closure_pair_of_orderOf x z hxord hzord hxz
      (mem_center_iff.mp z.property x)
    have hVe : IsElementaryAbelian 2 V :=
      { toIsMulCommutative := IsKleinFour.isMulCommutative
        exponent_dvd_p := by simp }
    exact hfour V hVe IsKleinFour.card_four
  have hOmega : omega₁ R (p := 2) = zpowers (z : R) := by
    apply le_antisymm
    · apply (Subgroup.closure_le _).mpr
      intro x hx
      have hxpow : x ^ 2 = 1 := by simpa using hx
      rcases huniq x hxpow with rfl | rfl
      · exact one_mem _
      · exact mem_zpowers _
    · apply zpowers_le.mpr
      apply Subgroup.subset_closure
      simpa using hzpow
  rw [hOmega, Nat.card_zpowers, hzord]

/-- Elementary rank at least three forces a four-group into a self-centralizing
two-core. -/
public theorem exists_elementary_four_le_pCore_of_characteristic_two
    {G : Type*} [Group G] [Finite G]
    (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (P : Sylow 2 G) (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hEP : E ≤ P) (hE : 8 ≤ Nat.card E) :
    ∃ V : Subgroup G, V ≤ pCore 2 G ∧ IsElementaryAbelian 2 V ∧ Nat.card V = 4 := by
  classical
  by_contra! hnone
  let R := pCore 2 G
  have hRne : R ≠ ⊥ := by
    intro hbot
    have hcent : centralizer (R : Set G) = ⊤ :=
      centralizer_eq_top_iff_subset.mpr (by
        rw [hbot]
        exact (bot_le : (⊥ : Subgroup G) ≤ center G))
    have htop : (⊤ : Subgroup G) ≤ ⊥ := by
      rw [← hcent, ← hbot]
      exact hchar
    have hEbot : E = ⊥ := bot_unique (le_top.trans htop)
    simp [hEbot] at hE
  let : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).mpr hRne
  have hnoneR : ∀ V : Subgroup R, IsElementaryAbelian 2 V → Nat.card V ≠ 4 := by
    intro V hV hcard
    let : IsElementaryAbelian 2 V := hV
    exact hnone (V.map R.subtype) (map_subtype_le V) IsElementaryAbelian.map_subtype
      ((card_map_of_injective R.subtype_injective).trans hcard)
  let O := omega₁ R (p := 2)
  let : O.Characteristic := omega₁_characteristic R
  let T := O.map R.subtype
  let : T.Normal := inferInstance
  have hTcard : Nat.card T = 2 :=
    (card_map_of_injective R.subtype_injective).trans
      (omega_card_two_of_no_four pCore_isPGroup hnoneR)
  have hTc : T ≤ center G := central_of_normal_card_two T hTcard
  let EP := E.subgroupOf P
  let : IsElementaryAbelian 2 EP := IsElementaryAbelian.subgroupOf hEP
  have hEPcard : 8 ≤ Nat.card EP := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hEP).toEquiv]
    exact hE
  obtain ⟨U, hUn, hUe, hUcard⟩ :=
    P.isPGroup'.exists_normal_four_of_elementary_rank_three EP hEPcard
  let : U.Normal := hUn
  let : IsElementaryAbelian 2 U := hUe
  let V := U.map (P : Subgroup G).subtype
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map_subtype
  have hPV : (P : Subgroup G) ≤ normalizer (V : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      U.le_normalizer_map (P : Subgroup G).subtype
  have hRV : ⁅R, V⁆ ≤ R ⊓ V :=
    le_inf (commutator_le_left R V)
      (le_normalizer_iff_commutator_le_right.mp
        ((pCore_isPGroup.le_sylow_of_normal P).trans hPV))
  have hRVT : ⁅R, V⁆ ≤ T := by
    intro x hx
    obtain ⟨hxR, hxV⟩ := hRV hx
    refine ⟨⟨x, hxR⟩, ?_, rfl⟩
    apply Subgroup.subset_closure
    apply Subtype.ext
    change x ^ (2 ^ 1) = 1
    simpa only [pow_one] using elemPow_eq_one_of_isElementaryAbelian (p := 2) x hxV
  have hTV : ⁅T, V⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (hTc.trans (center_le_centralizer _))
  have hW : IsPGroup 2 (normalClosure (V : Set G)) :=
    normalClosure_isPGroup_of_characteristicTwo T V hchar inferInstance hRVT hTV inferInstance
  have hVR : V ≤ R :=
    (le_normalClosure (H := V)).trans (le_sSup ⟨inferInstance, hW⟩)
  exact hnone V hVR inferInstance
    ((card_map_of_injective (P : Subgroup G).subtype_injective).trans hUcard)

/-- The solvable, trivial-odd-core form of the four-group existence theorem. -/
public theorem exists_elementary_four_le_pCore_of_solvable_oddCore_eq_bot
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    (hodd : pPrimeCore 2 G = ⊥)
    (P : Sylow 2 G) (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hEP : E ≤ P) (hE : 8 ≤ Nat.card E) :
    ∃ V : Subgroup G, V ≤ pCore 2 G ∧ IsElementaryAbelian 2 V ∧ Nat.card V = 4 := by
  apply exists_elementary_four_le_pCore_of_characteristic_two _ P E hEP hE
  rw [← Fitting_eq_pcore G 2 hodd]
  exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable inferInstance

/-- A four-group normalized by the two-core and containing an ambient central
involution lies in the two-core of a characteristic-two group. If its intersection
with the core had order two, all its commutators with the core would be central;
the characteristic-two normal-closure argument then gives the same containment. -/
public theorem elementary_four_le_pCore_of_normalized_of_central_involution
    {G : Type*} [Group G] [Finite G]
    (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (U : Subgroup G) [IsElementaryAbelian 2 U] (hU : Nat.card U = 4)
    (hQU : pCore 2 G ≤ normalizer (U : Set G))
    (t : G) (ht : orderOf t = 2) (htU : t ∈ U) (htZ : t ∈ center G) :
    U ≤ pCore 2 G := by
  classical
  by_contra hnot
  let Q := pCore 2 G
  let I := Q ⊓ U
  have hZQ : center G ≤ Q := (center_le_centralizer _).trans hchar
  have hTI : zpowers t ≤ I := zpowers_le.mpr ⟨hZQ htZ, htU⟩
  have hIne : Nat.card I ≠ 4 := by
    intro hc
    have heq : I = U := eq_of_le_of_card_ge inf_le_right (by omega)
    exact hnot (heq ▸ (inf_le_left : I ≤ Q))
  have hdiv : Nat.card I ∣ 2 ^ 2 := by
    simpa only [hU, Nat.reducePow] using card_dvd_of_le (show I ≤ U from inf_le_right)
  have hIle : Nat.card I ≤ 2 := by
    obtain ⟨k, hk, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
    interval_cases k
    · simpa only [hcard] using (show 2 ^ 0 ≤ 2 by decide)
    · simpa only [hcard] using (show 2 ^ 1 ≤ 2 by decide)
    · exact (hIne (by simpa only [Nat.reducePow] using hcard)).elim
  have hIT : I ≤ zpowers t := by
    have heq : zpowers t = I := eq_of_le_of_card_ge hTI (by
      simpa only [Nat.card_zpowers, ht] using hIle)
    exact heq.ge
  have hcomm : ⁅Q, U⁆ ≤ center G :=
    (le_inf (commutator_le_left Q U)
      (le_normalizer_iff_commutator_le_right.mp hQU)).trans
        (hIT.trans (zpowers_le.mpr htZ))
  have hW := normalClosure_isPGroup_of_characteristicTwo (center G) U hchar
    inferInstance hcomm
    (commutator_eq_bot_iff_le_centralizer.mpr (center_le_centralizer _)) inferInstance
  exact hnot ((le_normalClosure (H := U)).trans (le_sSup ⟨inferInstance, hW⟩))
