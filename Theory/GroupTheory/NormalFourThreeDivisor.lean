module

public import Theory.GroupTheory.PGroup.IndexTwoOmegaCenter
public import Theory.GroupTheory.PGroup.RankTwoNormalFour
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# Thompson's normal-four normalizer divisor

Let S be a Sylow two-subgroup with cyclic center and U a normal elementary
four-subgroup of S. If all ambient involutions are conjugate, then three
divides the order of the normalizer of the literal ambient image of U.

If three did not divide that normalizer, its image in Aut(U), of order
six, would be a two-group and would fix an involution z of U. In particular,
z is central in S. Put C = C_S(U). The index-two fixed-point bound gives
U = Ω₁(Z(C)), so U is characteristic in C. Fusion supplies a Sylow subgroup
T centralizing a different involution u of U and containing C. Since C has
index two in T, T normalizes U and therefore fixes z too. This gives two
distinct central involutions in T, contradicting the cyclic Sylow center.

Source: GLS, Volume 2, Lemma 16.21 (Thompson),
`refs/KGroup/GLS2/ChapterE.tex`, and its application in GLS, Volume 4,
Chapter 1, Lemma 3.10, `refs/KGroup/GLS4/Chapter1.tex`, lines 450–455.
The index-two estimate uses the action of S/C; the transcription's mention
of the action of u in the fixed-point step cannot be literal, since u ∈ Z(C).
-/

open Subgroup

namespace Sylow.NormalFourThreeDivisor

private theorem fixed_involution_of_three_not_dvd
    {G : Type*} [Group G] [Finite G]
    (U : Subgroup G) [IsElementaryAbelian 2 U] (hU : Nat.card U = 4)
    (hthree : ¬ 3 ∣ Nat.card (normalizer (U : Set G))) :
    ∃ z : U, orderOf z = 2 ∧ ∀ g : normalizer (U : Set G),
      g.val * (z : G) * g.val⁻¹ = z := by
  let : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour U := ⟨hU, IsElementaryAbelian.exponent_eq_prime⟩
  let f := U.normalizerMonoidHom
  have hd : Nat.card f.range ∣ 6 := by
    rw [← IsKleinFour.card_mulAut U]
    exact card_subgroup_dvd_card f.range
  have hn : ¬ 3 ∣ Nat.card f.range := fun h => hthree (h.trans (card_range_dvd f))
  have htwo : Nat.card f.range ∣ 2 := by
    have hle := Nat.le_of_dvd (by decide : 0 < 6) hd
    have hpos := Nat.card_pos (α := f.range)
    interval_cases h : Nat.card f.range <;> norm_num at *
  have hp : IsPGroup 2 f.range := IsPGroup.of_card_dvd_pow (n := 1) (by simpa using htwo)
  obtain ⟨z, hz, hzne⟩ := hp.exists_fixed_point_of_prime_dvd_card_of_fixed_point U
    (by rw [hU]; decide) (a := 1) (fun g => smul_one g)
  refine ⟨z, orderOf_eq_prime ?_ (Ne.symm hzne), ?_⟩
  · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 U) z
  · intro g
    exact congrArg Subtype.val (hz (f.rangeRestrict g))

private theorem omega_center_card_two
    {P : Type*} [Group P] [Finite P] [IsCyclic (center P)]
    (z : P) (hz : orderOf z = 2) (hzc : z ∈ center P) :
    Nat.card (omega₁ (center P) (p := 2)) = 2 := by
  let O := omega₁ (center P) (p := 2)
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative _
  let zO : O := ⟨⟨z, hzc⟩, subset_closure (by
    apply Subtype.ext
    change z ^ (2 ^ 1) = 1
    simpa only [pow_one, hz] using pow_orderOf_eq_one z)⟩
  have ho : orderOf zO = 2 := by
    rw [← orderOf_coe zO, ← orderOf_coe (zO : center P)]
    exact hz
  have hd : Nat.card O ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    exact IsElementaryAbelian.exponent_dvd_p 2 O
  have hd2 : 2 ∣ Nat.card O := by
    simpa only [ho] using (_root_.orderOf_dvd_natCard zO)
  exact Nat.dvd_antisymm hd hd2

private theorem normalizer_mapped_characteristic
    {P G : Type*} [Group P] [Group G]
    (C : Subgroup P) (F : Subgroup C) [F.Characteristic]
    (i : P →* G) (hi : Function.Injective i) :
    normalizer (C.map i : Set G) ≤ normalizer ((F.map C.subtype).map i : Set G) := by
  let e := C.equivMapOfInjective i hi
  let K := F.map e.toMonoidHom
  have hK : K.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    intro a x hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨(MulAut.congr e.symm a) y,
      characteristic_iff_le_comap.mp inferInstance (MulAut.congr e.symm a) hy, ?_⟩
    exact e.apply_symm_apply (a (e y))
  have he : (F.map C.subtype).map i = K.map (C.map i).subtype := by
    rw [map_map, map_map]
    rfl
  rw [he]
  exact normalizer_le_normalizer_characteristic_image (C.map i) K

private theorem centralizing_sylow
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (z : S) (hz : z ∈ center S) (t : G) (hconj : IsConj (z : G) t)
    (U : Subgroup G) (hUp : IsPGroup 2 U) (hUC : U ≤ centralizer ({t} : Set G)) :
    ∃ T : Sylow 2 G, U ≤ T ∧ (T : Subgroup G) ≤ centralizer ({t} : Set G) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  let a := MulAut.conj g
  let R := S.mapSurjective (f := a.toMonoidHom) a.surjective
  let C := centralizer ({t} : Set G)
  have hRC : (R : Subgroup G) ≤ C := by
    rintro _ ⟨s, hs, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have hcomm : (z : G) * s = s * z :=
      (congrArg Subtype.val (mem_center_iff.mp hz (⟨s, hs⟩ : S))).symm
    change a s * t = t * a s
    have ha : a (z : G) = t := hg
    rw [← ha, ← map_mul, ← map_mul, hcomm]
  obtain ⟨Q, hUQ⟩ := (hUp.comap_subtype (K := C)).exists_le_sylow
  let I := (Q : Subgroup C).map C.subtype
  have hUI : U ≤ I := by
    intro u hu
    exact ⟨⟨u, hUC hu⟩, hUQ hu, rfl⟩
  have hIcard : Nat.card I = Nat.card R := by
    rw [card_map_of_injective C.subtype_injective,
      Nat.card_congr (Q.equiv (R.subtype hRC)).toEquiv]
    exact Nat.card_congr (subgroupOfEquivOfLe hRC).toEquiv
  obtain ⟨T, hIT⟩ := (Q.isPGroup'.map C.subtype).exists_le_sylow
  have hITeq : I = (T : Subgroup G) := eq_of_le_of_card_ge hIT (by
    rw [hIcard, Nat.card_congr (R.equiv T).toEquiv])
  exact ⟨T, hITeq ▸ hUI, hITeq ▸ map_subtype_le (Q : Subgroup C)⟩

end Sylow.NormalFourThreeDivisor

open Sylow.NormalFourThreeDivisor in
/-- Thompson's normal-four consequence: full involution fusion and a cyclic
Sylow center force three to divide the normalizer of every normal four.
Normality is intrinsic to the Sylow subgroup; the normalizer is ambient. -/
public theorem Sylow.three_dvd_normalizer_card_of_normal_four {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (hcenter : IsCyclic (center S))
    (hfusion : ∀ z w : G, orderOf z = 2 → orderOf w = 2 → IsConj z w)
    (U : Subgroup S) [U.Normal] [IsElementaryAbelian 2 U] (hU : Nat.card U = 4) :
    3 ∣ Nat.card (normalizer (U.map (S : Subgroup G).subtype : Set G)) := by
  classical
  let i := (S : Subgroup G).subtype
  let V := U.map i
  have hV : Nat.card V = 4 := (card_map_of_injective (S : Subgroup G).subtype_injective).trans hU
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map i
  by_contra hthree
  obtain ⟨zV, hzV, hzfix⟩ := fixed_involution_of_three_not_dvd V hV hthree
  have hSN : (S : Subgroup G) ≤ normalizer (V : Set G) := by
    intro s hs
    apply U.le_normalizer_map i
    refine ⟨⟨s, hs⟩, ?_, rfl⟩
    rw [U.normalizer_eq_top]
    trivial
  let z : S := ⟨zV, (map_subtype_le U) zV.property⟩
  have hzU : z ∈ U := by
    obtain ⟨v, hv, he⟩ := zV.property
    exact (show v = z from Subtype.ext he) ▸ hv
  have hz : orderOf z = 2 := by
    rw [← orderOf_coe z, orderOf_coe zV]
    exact hzV
  have hzC : z ∈ center S := by
    apply mem_center_iff.mpr
    intro s
    exact Subtype.ext (mul_inv_eq_iff_eq_mul.mp (hzfix ⟨s, hSN s.property⟩))
  let : IsCyclic (center S) := hcenter
  have hZ := omega_center_card_two z hz hzC
  let C := centralizer (U : Set S)
  have hiC : C.index = 2 :=
    centralizer_index_eq_two_of_normal_four_of_card_omega_one_center_eq_two
      S.isPGroup' hZ U hU
  have hUC : U ≤ C := le_centralizer U
  let F := U.subgroupOf C
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.subgroupOf hUC
  have hF : Nat.card F = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hUC).toEquiv).trans hU
  have hFcenter : F ≤ center C := by
    intro u hu
    apply mem_center_iff.mpr
    intro c
    exact Subtype.ext (c.property u hu).symm
  have hFomega := omega_center_eq_four_of_index_two C hiC hZ F hFcenter hF
  let : (omega₁ (center C) (p := 2)).Characteristic := omega₁_characteristic _
  have hFchar : F.Characteristic := by
    rw [← hFomega]
    change ((omega₁ (center C) (p := 2)).map (center C).subtype).Characteristic
    infer_instance
  let Q := C.map i
  have hQN : normalizer (Q : Set G) ≤ normalizer (V : Set G) := by
    have hh := normalizer_mapped_characteristic C F i (S : Subgroup G).subtype_injective
    rwa [map_subgroupOf_eq_of_le hUC] at hh
  have hnot : ¬ U ≤ zpowers z := by
    intro h
    have hc := card_le_of_le h
    rw [hU, Nat.card_zpowers, hz] at hc
    omega
  obtain ⟨u, huU, huz⟩ := SetLike.not_le_iff_exists.mp hnot
  have hu1 : u ≠ 1 := fun h => huz (h ▸ one_mem _)
  have hu : orderOf u = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian u huU) hu1
  have hQu : Q ≤ centralizer ({(u : G)} : Set G) := by
    rintro _ ⟨c, hc, rfl⟩
    exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (hc u huU).symm)
  obtain ⟨T, hQT, hTu⟩ := centralizing_sylow S z hzC u
    (hfusion z u (by rwa [orderOf_coe]) (by rwa [orderOf_coe])) Q
    ((S.isPGroup'.to_subgroup C).map i) hQu
  have hQcard : Nat.card Q = Nat.card C := card_map_of_injective (S : Subgroup G).subtype_injective
  have hQTcard : Nat.card (Q.subgroupOf (T : Subgroup G)) = Nat.card C :=
    (Nat.card_congr (subgroupOfEquivOfLe hQT).toEquiv).trans hQcard
  have hiQT : (Q.subgroupOf (T : Subgroup G)).index = 2 := by
    have hc := (Q.subgroupOf (T : Subgroup G)).card_mul_index
    rw [hQTcard, ← Nat.card_congr (S.equiv T).toEquiv] at hc
    have hcS := C.card_mul_index
    rw [hiC] at hcS
    have hp := Nat.card_pos (α := C)
    nlinarith
  let : (Q.subgroupOf (T : Subgroup G)).Normal := normal_of_index_eq_two hiQT
  have hTN : (T : Subgroup G) ≤ normalizer (V : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hQT).mp inferInstance |>.trans hQN
  have huQ : (u : G) ∈ Q := mem_map_of_mem i (hUC huU)
  have hzQ : (z : G) ∈ Q := mem_map_of_mem i (hUC hzU)
  let uT : T := ⟨u, hQT huQ⟩
  let zT : T := ⟨z, hQT hzQ⟩
  have huTC : uT ∈ center T := by
    apply mem_center_iff.mpr
    intro t
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hTu t.property))
  have hzTC : zT ∈ center T := by
    apply mem_center_iff.mpr
    intro t
    exact Subtype.ext (mul_inv_eq_iff_eq_mul.mp (hzfix ⟨t, hTN t.property⟩))
  let : IsCyclic (center T) := (centerCongr (S.equiv T)).isCyclic.mp hcenter
  have he : (⟨uT, huTC⟩ : center T) = ⟨zT, hzTC⟩ :=
    IsCyclic.eq_of_orderOf_eq_two
      (by rw [← orderOf_coe, ← orderOf_coe]; exact (orderOf_coe u).trans hu)
      (by rw [← orderOf_coe, ← orderOf_coe]; exact (orderOf_coe z).trans hz)
  have huz' : u = z := Subtype.ext (congrArg (fun x : center T => ((x : T) : G)) he)
  exact huz (huz' ▸ mem_zpowers z)
