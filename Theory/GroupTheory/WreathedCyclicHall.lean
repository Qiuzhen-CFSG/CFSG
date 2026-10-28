module
public import Theory.GroupTheory.SemidihedralCyclicHall
public import Theory.GroupTheory.WreathedTwoFiveCenter
public import ABG.ChapterII.Section1.WreathedElementaryRank
public import Theory.GroupTheory.WreathedThirtyTwo
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Theory.GroupTheory.NormalCenterQuotient
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# Cyclic Hall actors with wreathed Sylow two-subgroups

A solvable group with a cyclic odd Hall subgroup and nonabelian Sylow
has nontrivial two-core. Its central involutions form a characteristic
subgroup of order two or four when the Sylow is C₄ wreath C₂. If three
does not divide the group order, wreathed fusion gives a cyclic normal
odd complement and every automorphism fixes the central Sylow involution.

For an ambient group whose order is not divisible by nine, a cubic
normalizing the odd Hall intersection lies in it whenever three divides
that intersection. Thus an excluded cubic-invariant four-group forces
all automorphisms preserving the intersection to fix the marked involution.
Neither the cubic nor those automorphisms need preserve the chosen Sylow.

Source: ABG II.1 Proposition 2, pp.11–13; Aschbacher–Smith 5.1.13,
printed p.636, refs/quasithin.pdf, the linear-three containing rows.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.WreathedCyclicHall
variable {G : Type*} [Group G] [Finite G]

private theorem odd_normal_le_hall (D N : Subgroup G) [N.Normal]
    (hD : IsHallSubgroup OddHall.oddPrimes D) (hN : Odd (Nat.card N)) : N ≤ D := by
  have hcop : Nat.Coprime (Nat.card N) D.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpN hpD
    have hp2 : p = 2 := Classical.not_not.mp
      (hD.p_in_pi_of_p_dvd_index ⟨p,hp⟩ hpD)
    exact hN.not_two_dvd_nat (hp2 ▸ hpN)
  have hd : D.relIndex N ∣ D.index := by
    rw [←relIndex_sup_of_normalizes N D le_normalizer_of_normal]
    exact relIndex_dvd_index_of_le le_sup_right
  exact relIndex_eq_one.mp
    (Nat.eq_one_of_dvd_coprimes hcop (relIndex_dvd_card D N) hd)

private theorem twoCore_ne_bot_of_cyclic_odd_hall
    (hs : Group.IsSolvable G) (D : Subgroup G) [IsCyclic D]
    (hD : IsHallSubgroup OddHall.oddPrimes D)
    (P : Subgroup G) (hP : IsPGroup 2 P) (hna : ¬ IsMulCommutative P) :
    pCore 2 G ≠ ⊥ := by
  intro htwo
  have hOD : pPrimeCore 2 G ≤ D := odd_normal_le_hall D _ hD
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  let : IsCyclic (pPrimeCore 2 G) :=
    isCyclic_of_injective (inclusion hOD) (inclusion_injective hOD)
  have hd : _root_.commutator G ≤ pPrimeCore 2 G :=
    (commutator_le_centralizer_of_isCyclic_normal (pPrimeCore 2 G)).trans
      (centralizer_pPrimeCore_le_of_pCore_eq_bot 2 hs htwo)
  have hc : ⁅P,P⁆ ≤ pPrimeCore 2 G :=
    (commutator_mono (show P ≤ ⊤ from le_top) le_top).trans hd
  have hdis : Disjoint P (pPrimeCore 2 G) := by
    obtain ⟨k,hk⟩ := hP.exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hk]
    exact pPrimeCore_coprime_card.pow_left k
  exact hna (commutator_self_eq_bot_iff.mp
    (le_bot_iff.mp ((le_inf (commutator_le_self P) hc).trans hdis.le_bot)))


/-- A characteristic elementary subgroup of order two or four in a solvable
wreathed group with cyclic odd Hall subgroup. -/
theorem characteristic_elementary_two_or_four
    (hs : Group.IsSolvable G) (D : Subgroup G) [IsCyclic D]
    (hD : IsHallSubgroup OddHall.oddPrimes D)
    (S : Sylow 2 G) (eS : S ≃* WreathedThirtyTwo) :
    ∃ E : Subgroup G, E.Characteristic ∧ IsElementaryAbelian 2 E ∧
      E ≤ (S : Subgroup G) ∧ (Nat.card E = 2 ∨ Nat.card E = 4) := by
  have hna : ¬ IsMulCommutative S := by
    intro hc
    let := hc
    apply wreathedThirtyTwo_not_commutative
    exact isMulCommutative_iff.mpr fun x y => eS.symm.injective (by
      simpa only [map_mul] using (isMulCommutative_iff.mp hc) (eS.symm x) (eS.symm y))
  have hcore := twoCore_ne_bot_of_cyclic_odd_hall hs D hD S S.isPGroup' hna
  let Q := pCore 2 G
  let : Nontrivial Q := (nontrivial_iff_ne_bot Q).mpr hcore
  let : (omega₁ (center Q) (p := 2)).Characteristic := omega₁_characteristic _
  let : IsElementaryAbelian 2 (omega₁ (center Q) (p := 2)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative _
  let E₀ := (omega₁ (center Q) (p := 2)).map (center Q).subtype
  let : IsElementaryAbelian 2 E₀ := IsElementaryAbelian.map_subtype
  let E := E₀.map Q.subtype
  let : E.Characteristic := inferInstance
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map_subtype
  have hEne : E ≠ ⊥ := fun h => omega_center_ne_bot (G := Q) pCore_isPGroup
    ((E₀.map_eq_bot_iff_of_injective Q.subtype_injective).mp h)
  have hES : E ≤ (S : Subgroup G) :=
    (map_subtype_le _).trans (pCore_isPGroup.le_sylow_of_normal S)
  let : IsElementaryAbelian 2 (E.subgroupOf (S : Subgroup G)) :=
    IsElementaryAbelian.subgroupOf hES
  have hb := ABG.elementary_card_le_four_of_isWreathedOfHeight
    (ABG.wreathed_equiv eS.symm ABG.RegularWreathHeightTwo.isWreathedOfHeight)
    (E.subgroupOf (S : Subgroup G))
  rw [Nat.card_congr (subgroupOfEquivOfLe hES).toEquiv] at hb
  obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hk2 : k ≤ 2 := by
    by_contra hn
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 3 ≤ k by omega)
    rw [←hk] at hh
    norm_num at hh
    omega
  refine ⟨E,inferInstance,inferInstance,hES,?_⟩
  interval_cases k
  · exact (hEne (eq_bot_of_card_eq _ (by simpa using hk))).elim
  · left; simpa using hk
  · right; simpa using hk

/-- The characteristic line is the central Sylow involution; the only
alternative is a characteristic four-group in the same Sylow subgroup. -/
theorem characteristic_involution_or_four
    (hs : Group.IsSolvable G) (D : Subgroup G) [IsCyclic D]
    (hD : IsHallSubgroup OddHall.oddPrimes D)
    (S : Sylow 2 G) (eS : S ≃* WreathedThirtyTwo)
    (z : S) (hz : orderOf z = 2) (hzc : z ∈ center S) :
    (zpowers (z : G)).Characteristic ∨
      ∃ E : Subgroup G, E.Characteristic ∧ IsElementaryAbelian 2 E ∧
        E ≤ (S : Subgroup G) ∧ Nat.card E = 4 := by
  obtain ⟨E,hchar,hE,hES,h2|h4⟩ := characteristic_elementary_two_or_four hs D hD S eS
  · left
    let := hchar
    let := hE
    have hEc := central_of_normal_card_two E h2
    obtain ⟨u,hu,hu1⟩ := E.bot_or_exists_ne_one.resolve_left
      (fun he => by simp [he] at h2)
    have hu2 : orderOf u = 2 := by
      exact (Nat.dvd_prime Nat.prime_two).mp
        (orderOf_dvd_of_pow_eq_one (elemPow_eq_one_of_isElementaryAbelian u hu)) |>.resolve_left
          (fun he => hu1 (orderOf_eq_one_iff.mp he))
    obtain ⟨P⟩ := ABG.Wreathed.nonempty_presentation
      (ABG.wreathed_equiv eS.symm ABG.RegularWreathHeightTwo.isWreathedOfHeight)
    let : IsCyclic (center S) := P.center_cyclic
    let uS : S := ⟨u,hES hu⟩
    have huSc : uS ∈ center S := mem_center_iff.mpr
      (fun s => Subtype.ext (mem_center_iff.mp (hEc hu) s))
    have he : (⟨uS,huSc⟩ : center S) = ⟨z,hzc⟩ := IsCyclic.eq_of_orderOf_eq_two
      ((orderOf_coe _).symm.trans ((orderOf_coe uS).symm.trans hu2))
      ((orderOf_coe _).symm.trans hz)
    have huz : u = (z : G) := congrArg (fun x : center S => x.val.val) he
    have hsub : zpowers (z : G) ≤ E := zpowers_le.mpr (huz ▸ hu)
    have heq : zpowers (z : G) = E := eq_of_le_of_card_ge hsub (by
      rw [Nat.card_zpowers,orderOf_coe,hz,h2])
    rw [heq]
    infer_instance
  · exact .inr ⟨E,hchar,hE,hES,h4⟩

private theorem normal_complement (S : Sylow 2 G) (eS : S ≃* WreathedThirtyTwo)
    (h3 : ¬ 3 ∣ Nat.card G) : HasNormalPComplement 2 G := by
  have hS : ABG.IsWreathedOfHeight S 2 :=
    ABG.wreathed_equiv eS.symm ABG.RegularWreathHeightTwo.isWreathedOfHeight
  obtain ⟨P⟩ := ABG.Wreathed.nonempty_presentation hS
  let U := P.U.map (S : Subgroup G).subtype
  let V := P.V.map (S : Subgroup G).subtype
  have hf := P.fusionFrame S
  have hu : ABG.automizerIndex U = 2 :=
    (ABG.Wreathed.u_automizer_index S 2 U V hf).resolve_right (by
      intro he
      apply h3
      exact (show 3 ∣ 6 by decide).trans (he ▸
        (relIndex_dvd_card (centralizer (U : Set G)) (normalizer (U : Set G))).trans
          (normalizer (U : Set G)).card_subgroup_dvd_card))
  have hv : ABG.outerAutomizerIndex V = 2 :=
    (ABG.Wreathed.v_outer_automizer_index S 2 U V hf).resolve_right (by
      intro he
      apply h3
      exact (show 3 ∣ 6 by decide).trans (he ▸
        (relIndex_dvd_card (V ⊔ centralizer (V : Set G)) (normalizer (V : Set G))).trans
          (normalizer (V : Set G)).card_subgroup_dvd_card))
  exact ABG.hasNormalTwoComplement_of_cyclic_focalSubgroupOf S (by
    rw [(ABG.Wreathed.focal_subgroup_cases S P).1 hu hv]
    exact P.derived_structure.2.1)

private theorem central_involution_derived
    {Q : Type*} [Group Q] [Finite Q] (e : Q ≃* WreathedThirtyTwo)
    (z : Q) (hz : orderOf z = 2) (hc : z ∈ center Q) : z ∈ commutator Q := by
  obtain ⟨P⟩ := ABG.Wreathed.nonempty_presentation
    (ABG.wreathed_equiv e.symm ABG.RegularWreathHeightTwo.isWreathedOfHeight)
  let : IsCyclic (center Q) := P.center_cyclic
  have he : (⟨z,hc⟩ : center Q) = ⟨P.x,P.x_mem_center⟩ :=
    IsCyclic.eq_of_orderOf_eq_two ((orderOf_coe _).symm.trans hz)
      ((orderOf_coe _).symm.trans P.x_orderOf)
  have hzP : z = P.x := congrArg Subtype.val he
  rw [hzP,←P.r_half,P.derived_structure.1]
  exact (zpowers P.r).pow_mem (mem_zpowers _) _

/-- Without a factor three, wreathed fusion yields a cyclic normal odd
complement. Every automorphism fixes the central Sylow involution. -/
theorem fixed_central_involution_of_three_not_dvd
    (D : Subgroup G) [IsCyclic D] (hD : IsHallSubgroup OddHall.oddPrimes D)
    (h3 : ¬ 3 ∣ Nat.card G) (S : Sylow 2 G) (eS : S ≃* WreathedThirtyTwo)
    (z : S) (hz : orderOf z = 2) (hc : z ∈ center S) (φ : MulAut G) :
    φ (z : G) = z := by
  obtain ⟨N,hN,hcop,hquot⟩ := normal_complement S eS h3
  let : N.Normal := hN
  have hND : N ≤ D := odd_normal_le_hall D N hD (Nat.coprime_two_left.mp hcop)
  let : IsCyclic N := isCyclic_of_injective (inclusion hND) (inclusion_injective hND)
  have hzcomm : (z : G) ∈ commutator G := by
    have hh := mem_map_of_mem (S : Subgroup G).subtype (central_involution_derived eS z hz hc)
    rw [map_commutator_eq] at hh
    exact commutator_mono le_top le_top hh
  have hzN : (z : G) ∈ centralizer (N : Set G) :=
    commutator_le_centralizer_of_isCyclic_normal N hzcomm
  have hzcentral : (z : G) ∈ center G := by
    apply mem_center_iff.mpr
    intro y
    have hall : N ⊔ (S : Subgroup G) ≤ centralizer ({(z : G)} : Set G) := by
      apply sup_le
      · intro n hn
        exact mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hzN) n hn)
      · intro s hs
        exact mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_center_iff.mp hc (⟨s,hs⟩ : S)))
    have hy := hall (show y ∈ N ⊔ (S : Subgroup G) from by
      rw [sup_comm,S.sup_eq_top_of_quotient_isPGroup N hquot]; trivial)
    exact mem_centralizer_singleton_iff.mp hy
  have hpz : φ (z : G) ∈ center G := (centerCongr φ ⟨z,hzcentral⟩).property
  have hpord : orderOf (φ (z : G)) = 2 := (φ.orderOf_eq _).trans ((orderOf_coe z).trans hz)
  have hps : φ (z : G) ∈ S := by
    let Q := zpowers (φ (z : G))
    have hQc : Q ≤ center G := zpowers_le.mpr hpz
    let : Q.Normal := ⟨fun x hx g => by
      have hc := mem_center_iff.mp (hQc hx) g
      simpa only [hc,mul_inv_cancel_right] using hx⟩
    have hQp : IsPGroup 2 Q := IsPGroup.of_card (n := 1) (by
      simpa only [Q,Nat.card_zpowers,pow_one] using hpord)
    exact hQp.le_sylow_of_normal S (mem_zpowers _)
  obtain ⟨P⟩ := ABG.Wreathed.nonempty_presentation
    (ABG.wreathed_equiv eS.symm ABG.RegularWreathHeightTwo.isWreathedOfHeight)
  let : IsCyclic (center S) := P.center_cyclic
  let zz : center S := ⟨z,hc⟩
  let ww : center S := ⟨⟨φ z,hps⟩,mem_center_iff.mpr
    (fun s => Subtype.ext (mem_center_iff.mp hpz s))⟩
  have he : ww = zz := IsCyclic.eq_of_orderOf_eq_two
    ((orderOf_coe ww).symm.trans ((orderOf_coe ww.val).symm.trans hpord))
    ((orderOf_coe zz).symm.trans hz)
  exact congrArg (fun x : center S => x.val.val) he

end Theory.GroupTheory.WreathedCyclicHall

namespace Theory.GroupTheory.WreathedCyclicHall
variable {G : Type*} [Group G] [Finite G]
private theorem cubic_le_of_normalizes (D B : Subgroup G)
    (h9 : ¬ 9 ∣ Nat.card G) (h3 : 3 ∣ Nat.card D) (hB : Nat.card B = 3)
    (hBD : B ≤ normalizer (D : Set G)) : B ≤ D := by
  have hd : Nat.card (D ⊓ B : Subgroup G) ∣ 3 := by
    rw [←hB]
    exact card_dvd_of_le inf_le_right
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with hi | hi
  · have he := card_mul_eq_card_inf_mul_card_sup_of_normalizes D B hBD
    rw [hi,hB,one_mul] at he
    have hh : 9 ∣ Nat.card (D ⊔ B : Subgroup G) := by
      rw [←he]
      simpa using Nat.mul_dvd_mul h3 (dvd_refl 3)
    exact (h9 (hh.trans (D ⊔ B : Subgroup G).card_subgroup_dvd_card)).elim
  · have he : D ⊓ B = B := eq_of_le_of_card_ge inf_le_right (by rw [hB,hi])
    exact he ▸ inf_le_left

/-- A normalizing cubic rules out the characteristic four alternative.
No normalization of the chosen Sylow subgroup by that cubic is assumed. -/
theorem automorphism_fix_of_cubic_normalizer
    (h9 : ¬ 9 ∣ Nat.card G)
    (J : Subgroup G) (hs : Group.IsSolvable J)
    (D : Subgroup J) [IsCyclic D] (hD : IsHallSubgroup OddHall.oddPrimes D)
    (B : Subgroup G) (hB : Nat.card B = 3)
    (hBD : B ≤ normalizer (D.map J.subtype : Set G))
    (S : Sylow 2 G) (eS : S ≃* WreathedThirtyTwo) (hSJ : (S : Subgroup G) ≤ J)
    (hno : ∀ E : Subgroup G, E ≤ (S : Subgroup G) → IsElementaryAbelian 2 E →
      Nat.card E = 4 → ¬ B ≤ normalizer (E : Set G))
    (z : S) (hz : orderOf z = 2) (hc : z ∈ center S)
    (φ : MulAut G) (hJ : J.map φ.toMonoidHom = J) : φ (z : G) = z := by
  let P := S.subtype hSJ
  let eP : P ≃* S := (subgroupOfEquivOfLe hSJ)
  let zP := eP.symm z
  have hzP : orderOf zP = 2 := (eP.symm.orderOf_eq _).trans hz
  have hcP : zP ∈ center P := by
    apply mem_center_iff.mpr
    intro x
    apply eP.injective
    simpa only [map_mul,zP,MulEquiv.apply_symm_apply] using mem_center_iff.mp hc (eP x)
  let ψ : MulAut J := (φ.subgroupMap J).trans (MulEquiv.subgroupCongr hJ)
  by_cases h3 : 3 ∣ Nat.card J
  · have h3D : 3 ∣ Nat.card D := by
      rw [←D.card_mul_index] at h3
      exact (Nat.prime_three.dvd_mul.mp h3).resolve_right (fun hh =>
        hD.p_in_pi_of_p_dvd_index ⟨3,Nat.prime_three⟩ hh (by change (3 : ℕ) ≠ 2; decide))
    have hBJ : B ≤ J := (cubic_le_of_normalizes (D.map J.subtype) B h9
      (by rwa [card_map_of_injective J.subtype_injective]) hB hBD).trans (map_subtype_le _)
    rcases characteristic_involution_or_four hs D hD P (eP.trans eS) zP hzP hcP with hline | ⟨E,hE,hEA,hEP,hE4⟩
    · let := hline
      have hm : ψ (zP : J) ∈ zpowers (zP : J) :=
        characteristic_iff_le_comap.mp hline ψ (mem_zpowers _)
      let : IsCyclic (zpowers (zP : J)) := inferInstance
      have he : (⟨ψ (zP : J),hm⟩ : zpowers (zP : J)) = ⟨zP,mem_zpowers _⟩ :=
        IsCyclic.eq_of_orderOf_eq_two
          ((orderOf_coe _).symm.trans ((ψ.orderOf_eq _).trans ((orderOf_coe zP).trans hzP)))
          ((orderOf_coe _).symm.trans ((orderOf_coe zP).trans hzP))
      exact congrArg (fun x : zpowers (zP : J) => x.val.val) he
    · let := hE
      let := hEA
      have hES : E.map J.subtype ≤ (S : Subgroup G) := by
        rintro x ⟨y,hy,rfl⟩
        exact hEP hy
      have hBN : B ≤ normalizer (E.map J.subtype : Set G) :=
        (hBJ.trans J.le_normalizer).trans (normalizer_le_normalizer_characteristic_image J E)
      exact (hno (E.map J.subtype) hES IsElementaryAbelian.map_subtype
        (by rwa [card_map_of_injective J.subtype_injective]) hBN).elim
  · have he := fixed_central_involution_of_three_not_dvd D hD h3 P (eP.trans eS) zP hzP hcP ψ
    exact congrArg J.subtype he
end Theory.GroupTheory.WreathedCyclicHall
