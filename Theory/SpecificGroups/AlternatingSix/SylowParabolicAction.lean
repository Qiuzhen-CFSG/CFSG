module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.MaximalSylow
public import Theory.SpecificGroups.AlternatingSix.AlternatingFourActions

/-!
# Index-three Sylow overgroups preserve the natural A₆ action

Let C be a normal A₆, let S be Sylow two, and suppose C S generates the
ambient group. An overgroup P of S with |P:S| = 3 has |P ∩ C| = 24.
Its characteristic two-core is a Klein four group. Since P normalizes
that four group, P acts through the natural S₆ automorphisms of C.
Together with C, the Sylow subgroup generates the whole ambient action.

The order-24 core argument reuses the elementary proof in
`ShadowLocal.MaximalSylow`, whose auxiliary declarations are private.
This extension leaves that established module boundary unchanged.
The actual representation consumer is the A₆ head selection in 13.8.26.
Source: Aschbacher–Smith 13.8.21(3), 13.8.26, printed pp.956–957,962,
with the four-group geometry of I.5.
-/

public section
open Subgroup AlternatingSix.ShadowLocal
namespace AlternatingSix.SylowParabolicAction

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


variable {J : Type*} [Group J] [Finite J]

/-- The original parabolic meets the normal A₆ in a group of order 24. -/
theorem inner_parabolic_card (C : Subgroup J) [C.Normal] (e : C ≃* A6)
    (S : Sylow 2 J) (P : Subgroup J) (hSP : (S : Subgroup J) ≤ P)
    (hgen : C ⊔ (S : Subgroup J) = ⊤)
    (hi : (S : Subgroup J).relIndex P = 3) :
    Nat.card (P.subgroupOf C) = 24 := by
  obtain ⟨Q, hQ⟩ := S.exists_subgroupOf_eq_of_normal C
  have hQC : Nat.card Q = 8 := by
    let Q' := Q.mapSurjective (f := e.toMonoidHom) e.surjective
    have hc := alternatingSylow_card Q'
    rwa [show Nat.card Q' = Nat.card Q from card_map_of_injective e.injective] at hc
  have hCP : C ⊔ P = ⊤ := top_unique (hgen ▸ sup_le_sup_left hSP C)
  have hCS : C.relIndex (S : Subgroup J) = C.index := by
    rw [← relIndex_sup_left, hgen, relIndex_top_right]
  have hCPi : C.relIndex P = C.index := by
    rw [← relIndex_sup_left, hCP, relIndex_top_right]
  have hmul := relIndex_inf_mul_relIndex (S : Subgroup J) C P
  have hmul' := relIndex_mul_relIndex ((S : Subgroup J) ⊓ C) S P inf_le_left hSP
  rw [inf_relIndex_left, hCS, hi] at hmul'
  rw [hCPi, ← hmul', mul_comm C.index 3] at hmul
  have hrel : (S : Subgroup J).relIndex (C ⊓ P) = 3 :=
    Nat.mul_right_cancel (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := C))) hmul
  have hiQ : (Q : Subgroup C).relIndex (P.subgroupOf C) = 3 := by
    rw [hQ, subgroupOf, relIndex_comap, subgroupOf, map_comap_eq, range_subtype, inf_comm]
    simpa only [inf_comm] using hrel
  have hQP : (Q : Subgroup C) ≤ P.subgroupOf C := by rw [hQ]; exact comap_mono hSP
  have hc := relIndex_mul_relIndex (⊥ : Subgroup C) Q (P.subgroupOf C) bot_le hQP
  rw [relIndex_bot_left, relIndex_bot_left, hQC, hiQ] at hc
  omega

/-- The original index-three parabolic forces the entire action to be natural. -/
theorem parabolic_natural (C : Subgroup J) [C.Normal] (e : C ≃* A6)
    (S : Sylow 2 J) (P : Subgroup J) (hSP : (S : Subgroup J) ≤ P)
    (hgen : C ⊔ (S : Subgroup J) = ⊤)
    (hi : (S : Subgroup J).relIndex P = 3) :
    (conjugationAction C e).range ≤ natural := by
  let B := P.subgroupOf C
  let B' := B.map e.toMonoidHom
  have hcB : Nat.card B' = 24 := by
    rw [card_map_of_injective e.injective]
    exact inner_parabolic_card C e S P hSP hgen hi
  let F := B.pCoreIn 2
  let F' := B'.pCoreIn 2
  let : IsKleinFour F' := core_isKleinFour_of_card_twentyFour B' hcB
  have heF : F.map e.toMonoidHom = F' := map_pCoreIn_of_injective 2 B e.toMonoidHom e.injective
  let eF : F ≃* F' := (F.equivMapOfInjective e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr heF)
  let : IsKleinFour F := {
    card_four := (Nat.card_congr eF.toEquiv).trans IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eF).trans IsKleinFour.exponent_two }
  let U := F.map C.subtype
  let eU : F ≃* U := F.equivMapOfInjective C.subtype C.subtype_injective
  let : IsKleinFour U := {
    card_four := (Nat.card_congr eU.toEquiv).symm.trans IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eU).symm.trans IsKleinFour.exponent_two }
  have hUK : U ≤ C := by
    simpa only [range_subtype] using map_le_range C.subtype F
  have hP : P ≤ normalizer (U : Set J) := by
    have hb : P ≤ normalizer (C ⊓ P : Set J) :=
      (le_inf (C.normalizer_eq_top ▸ le_top) P.le_normalizer).trans inf_normalizer_le_normalizer_inf
    have he : U = (C ⊓ P).pCoreIn 2 := by
      rw [show U = (B.pCoreIn 2).map C.subtype from rfl,
        map_pCoreIn_of_injective 2 B C.subtype C.subtype_injective, show B.map C.subtype = C ⊓ P by
          change (P.subgroupOf C).map C.subtype = C ⊓ P
          rw [subgroupOf, map_comap_eq, range_subtype]]
    rw [he]
    exact hb.trans (normalizer_le_normalizer_characteristic_image (C ⊓ P) (pCore 2 ↥(C ⊓ P)))
  have hSn := conjugationAction_map_natural_of_normalizes_four C e U (S : Subgroup J) hUK (hSP.trans hP)
  have hCn : C.map (conjugationAction C e) ≤ natural := by
    rw [conjugationAction_map_inner]
    exact inner_le_natural
  rw [MonoidHom.range_eq_map, ← hgen, Subgroup.map_sup]
  exact sup_le hCn hSn


end AlternatingSix.SylowParabolicAction
