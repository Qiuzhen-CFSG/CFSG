module

public import Theory.SpecificGroups.AlternatingSix.ProperSylowOvergroups
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.CharacteristicCentralizerFusion

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Dihedral
public import Theory.GroupTheory.DihedralGeneratedFactor
public import Theory.GroupTheory.NormalCenterQuotient
public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.GroupTheory.IndexNormal

public section

open Subgroup
namespace AlternatingSix.ShadowLocal

private theorem normal_two_false (B : Subgroup A6) (hB : Nat.card B = 24)
    (Z : Subgroup B) [Z.Normal] (hZ : Nat.card Z = 2) : False := by
  have hcentral := central_of_normal_card_two Z hZ
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 (by rw [hZ])
  have hzA : orderOf (z.val.val : A6) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have hBC : B ≤ centralizer ({z.val.val} : Set A6) := by
    intro b hb
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (mem_center_iff.mp (hcentral z.property) ⟨b, hb⟩)
  have hc : Nat.card (centralizer ({z.val.val} : Set A6)) = 8 := by
    rw [← inner_fixed_eq_centralizer]
    exact inner_involution_fixed_card _ hzA
  have hd := card_dvd_of_le hBC
  rw [hB, hc] at hd
  norm_num at hd

private theorem cyclic_characteristic {G : Type*} [Group G] [IsCyclic G]
    (K : Subgroup G) : K.Characteristic := by
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic G)
  obtain ⟨n, rfl⟩ := (Subgroup.le_zpowers_iff g K).mp (by rw [hg]; exact le_top)
  apply Subgroup.characteristic_iff_map_le.mpr
  intro φ
  rw [MonoidHom.map_zpowers, Subgroup.zpowers_le, map_pow]
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg ▸ Subgroup.mem_top (φ g))
  change (φ g) ^ n ∈ Subgroup.zpowers (g ^ n)
  rw [← hi]
  have he : (g ^ i) ^ n = (g ^ n) ^ i := by
    rw [← zpow_natCast (g ^ i), ← zpow_mul, mul_comm i, zpow_mul, zpow_natCast]
  rw [he]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _

private theorem cyclic_four_false (B : Subgroup A6) (hB : Nat.card B = 24)
    (R : Subgroup B) [R.Normal] [IsCyclic R] (hR : Nat.card R = 4) : False := by
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := R) 2 (by rw [hR]; decide)
  let Z := zpowers z
  let : Z.Characteristic := cyclic_characteristic Z
  let W := Z.map R.subtype
  let : W.Normal := ConjAct.normal_of_characteristic_of_normal
  apply normal_two_false B hB W
  rw [card_map_of_injective R.subtype_injective, Nat.card_zpowers, hz]

private theorem sylow_dihedral (B : Subgroup A6) (hB : Nat.card B = 24)
    (P : Sylow 2 B) : Nonempty (P ≃* DihedralGroup 4) := by
  have hP : Nat.card P = 8 := by
    rw [Sylow.card_eq_multiplicity, hB]
    decide +kernel
  obtain ⟨Q, hQ⟩ := (P.isPGroup'.map B.subtype).exists_le_sylow
  have he : (P : Subgroup B).map B.subtype = (Q : Subgroup A6) :=
    eq_of_le_of_card_ge hQ (by rw [card_map_of_injective B.subtype_injective,
      hP, alternatingSylow_card])
  obtain ⟨e⟩ := alternatingSylow_dihedral Q
  exact ⟨((P : Subgroup B).equivMapOfInjective B.subtype B.subtype_injective).trans
    ((MulEquiv.subgroupCongr he).trans e)⟩

private theorem internal_core_isKleinFour (B : Subgroup A6) (hB : Nat.card B = 24) :
    IsKleinFour (pCore 2 B) := by
  let P : Sylow 2 B := Classical.choice inferInstance
  have hP : Nat.card P = 8 := by
    rw [Sylow.card_eq_multiplicity, hB]
    decide +kernel
  have hi : (P : Subgroup B).index = 3 := by
    have h := (P : Subgroup B).card_mul_index
    rw [hP, hB] at h
    omega
  let R := pCore 2 B
  have hRP : R ≤ (P : Subgroup B) := pCore_isPGroup.le_sylow_of_normal P
  have hCR : (P : Subgroup B).normalCore ≤ R :=
    le_sSup ⟨inferInstance, P.isPGroup'.to_le (P : Subgroup B).normalCore_le⟩
  have hfac : (P : Subgroup B).normalCore.index ∣ 6 := by
    have h : (P : Subgroup B).normalCore.index ∣ (P : Subgroup B).index.factorial := by
      rw [normalCore_eq_ker, index_ker, index_eq_card, ← Nat.card_perm]
      exact card_subgroup_dvd_card _
    simpa [hi, Nat.factorial] using h
  have hCge : 4 ≤ Nat.card (P : Subgroup B).normalCore := by
    have hbound := Nat.le_of_dvd (by decide : 0 < 6) hfac
    have hprod := (P : Subgroup B).normalCore.card_mul_index
    rw [hB] at hprod
    nlinarith
  have hRge : 4 ≤ Nat.card R := hCge.trans
    (Nat.le_of_dvd (Nat.card_pos (α := R)) (card_dvd_of_le hCR))
  have hRd : Nat.card R ∣ 8 := hP ▸ card_dvd_of_le hRP
  have hR8 : Nat.card R ≠ 8 := by
    intro h8
    have he : R = (P : Subgroup B) := eq_of_le_of_card_ge hRP (by rw [h8, hP])
    obtain ⟨e⟩ := sylow_dihedral B hB P
    have ez : R ≃* DihedralGroup 4 := (MulEquiv.subgroupCongr he).trans e
    have hz : Nat.card (center R) = 2 := DihedralGroup.center_card_of_equiv (n := 2)
      (by decide) ez
    let Z := (center R).map R.subtype
    let : Z.Normal := ConjAct.normal_of_characteristic_of_normal
    exact normal_two_false B hB Z ((card_map_of_injective R.subtype_injective).trans hz)
  have hR4 : Nat.card R = 4 := by
    obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show Nat.card R ∣ 2 ^ 3 from hRd)
    interval_cases k <;> simp_all
  have hnoncyclic : ¬ IsCyclic R := by
    intro hc
    let := hc
    exact cyclic_four_false B hB R hR4
  let : Nontrivial R := (Finite.one_lt_card_iff_nontrivial).mp (by omega)
  refine ⟨hR4, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr ?_⟩
  intro g hg
  have hd : orderOf g ∣ 4 := hR4 ▸ orderOf_dvd_natCard g
  have hn : orderOf g ≠ 1 := by simpa using hg
  have h4 : orderOf g ≠ 4 := fun h => hnoncyclic
    (isCyclic_of_orderOf_eq_card g (h.trans hR4.symm))
  obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show orderOf g ∣ 2 ^ 2 from hd)
  interval_cases k
  · exact (hn he).elim
  · exact he
  · exact (h4 he).elim

private theorem core_isKleinFour_of_card_twentyFour (B : Subgroup A6) (hB : Nat.card B = 24) :
    IsKleinFour (B.pCoreIn 2) := by
  let h := internal_core_isKleinFour B hB
  let e := (pCore 2 B).equivMapOfInjective B.subtype B.subtype_injective
  exact ⟨(Nat.card_congr e.toEquiv).symm.trans h.card_four,
    (Monoid.exponent_eq_of_mulEquiv e).symm.trans h.exponent_two⟩


private theorem inner_part_card (R : Subgroup AutA6) :
    Nat.card (R.comap (MulAut.conj : A6 →* AutA6)) =
      Nat.card (inner.subgroupOf R) := by
  have he : (R.comap (MulAut.conj : A6 →* AutA6)).map
      (MulAut.conj : A6 →* AutA6) = (inner.subgroupOf R).map R.subtype := by
    rw [map_comap_eq, subgroupOf, map_comap_eq, range_subtype]
    exact inf_comm _ _
  calc
    _ = Nat.card ((R.comap (MulAut.conj : A6 →* AutA6)).map
        (MulAut.conj : A6 →* AutA6)) := (card_map_of_injective inner_injective).symm
    _ = Nat.card ((inner.subgroupOf R).map R.subtype) :=
      congrArg (fun V : Subgroup AutA6 => Nat.card V) he
    _ = _ := card_map_of_injective R.subtype_injective

private theorem card_le_four_mul_inner_part (R : Subgroup AutA6) :
    Nat.card R ≤ Nat.card (R.comap (MulAut.conj : A6 →* AutA6)) * 4 := by
  have hd : (inner.subgroupOf R).index ∣ 4 := by
    change (inner.comap R.subtype).index ∣ 4
    rw [index_comap]
    exact inner_index ▸ inner.relIndex_dvd_index_of_normal R.subtype.range
  have hi := Nat.le_of_dvd (by decide : 0 < 4) hd
  calc
    Nat.card R = Nat.card (inner.subgroupOf R) * (inner.subgroupOf R).index :=
      (inner.subgroupOf R).card_mul_index.symm
    _ ≤ Nat.card (inner.subgroupOf R) * 4 := Nat.mul_le_mul_left _ hi
    _ = _ := by rw [inner_part_card]

private theorem inner_part_contains_sylow (P : Sylow 2 AutA6)
    (R : Subgroup AutA6) (hPR : (P : Subgroup AutA6) ≤ R) :
    ∃ Q : Sylow 2 A6, (Q : Subgroup A6) ≤ R.comap (MulAut.conj : A6 →* AutA6) := by
  let D := (P : Subgroup AutA6).comap (MulAut.conj : A6 →* AutA6)
  have hD : Nat.card D = 8 := (inner_part_card (P : Subgroup AutA6)).trans
    (sylowInner_card P)
  have hp : IsPGroup 2 D := P.isPGroup'.comap_of_injective _ inner_injective
  obtain ⟨Q, hDQ⟩ := hp.exists_le_sylow
  have hDeq : D = (Q : Subgroup A6) := eq_of_le_of_card_ge hDQ
    (by rw [alternatingSylow_card, hD])
  exact ⟨Q, hDeq ▸ comap_mono hPR⟩

private theorem inner_core_normalized (R : Subgroup AutA6) :
    R ≤ normalizer
      (((R.comap (MulAut.conj : A6 →* AutA6)).pCoreIn 2).map
        (MulAut.conj : A6 →* AutA6) : Set AutA6) := by
  rw [map_pCoreIn_of_injective 2 _ _ inner_injective]
  have hb : R ≤ normalizer
      ((R.comap (MulAut.conj : A6 →* AutA6)).map
        (MulAut.conj : A6 →* AutA6) : Set AutA6) := by
    rw [map_comap_eq]
    change R ≤ normalizer (inner ⊓ R : Set AutA6)
    apply (le_inf ?_ R.le_normalizer).trans inf_normalizer_le_normalizer_inf
    rw [normalizer_eq_top]
    exact le_top
  exact hb.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

theorem sylow_isCoatom
    (P : Sylow 2 AutA6) : IsCoatom (P : Subgroup AutA6) := by
  refine ⟨?_, ?_⟩
  · intro he
    have hc := congrArg (fun V : Subgroup AutA6 => Nat.card V) he
    rw [sylow_card, card_top, card_aut] at hc
    omega
  · intro R hPR
    let B := R.comap (MulAut.conj : A6 →* AutA6)
    by_cases hB : B = ⊤
    · have hi : inner ≤ R := by
        rintro _ ⟨a, rfl⟩
        exact show a ∈ B from hB ▸ mem_top a
      have h360 : 360 ∣ Nat.card R := card_inner ▸ card_dvd_of_le hi
      have h32 : 32 ∣ Nat.card R := sylow_card P ▸ card_dvd_of_le hPR.le
      have hfull : 1440 ∣ Nat.card R := by
        have h := Nat.lcm_dvd h360 h32
        norm_num at h
        exact h
      have hc : Nat.card R = 1440 := Nat.dvd_antisymm
        (card_aut ▸ R.card_subgroup_dvd_card) hfull
      exact eq_top_of_card_eq R (hc.trans card_aut.symm)
    · obtain ⟨Q, hQB⟩ := inner_part_contains_sylow P R hPR.le
      rcases ProperSylowOvergroups.card_eight_or_twentyFour Q B hQB hB with h8 | h24
      · have hbound := card_le_four_mul_inner_part R
        change Nat.card R ≤ Nat.card B * 4 at hbound
        rw [h8] at hbound
        exact (hPR.ne (eq_of_le_of_card_ge hPR.le
          (by rw [sylow_card]; omega))).elim
      · let : IsKleinFour (B.pCoreIn 2) := core_isKleinFour_of_card_twentyFour B h24
        have hPN := hPR.le.trans (inner_core_normalized R)
        have hd := card_dvd_of_le hPN
        rw [sylow_card, four_aut_normalizer_card (B.pCoreIn 2)] at hd
        norm_num at hd

end AlternatingSix.ShadowLocal

#print axioms AlternatingSix.ShadowLocal.sylow_isCoatom
