module

public import Theory.GroupTheory.PGroup.CriticalQuaternionCentralizer
public import Theory.GroupTheory.PGroup.NonelementaryCenterQuotientBound
public import Theory.ThreeSubgroups

/-!
# The centralizer of a critical quaternion center

If a critical subgroup has a quaternion supplement to its center, the
centralizer of that center is again critical, with the same center.
Quaternion elements have fourth power one, so their ambient displacements
are central involutions. The three-subgroups lemma controls commutators
with the larger centralizer, and squaring kills its commutators with the
original critical subgroup.

Source: MacWilliams, Trans. AMS 150 (1970), §3(ii)–(iv), pp.366–368.
-/

open Subgroup
open scoped commutatorElement IsMulCommutative

namespace IsCriticalPSubgroup

/-- Centralizing the center of a critical quaternion extension gives another
critical subgroup, with the same ambient image of its center. -/
public theorem center_centralizer_isCritical_of_quaternion_supplement
    {P : Type*} [Group P] [Finite P]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    {C : Subgroup P} (hC : IsCriticalPSubgroup 2 C)
    (R : Subgroup C) (eR : R ≃* QuaternionGroup 2)
    (hRgen : R ⊔ center C = ⊤) :
    let Z := (center C).map C.subtype
    let M := centralizer (Z : Set P)
    IsCriticalPSubgroup 2 M ∧ (center M).map M.subtype = Z := by
  let Z : Subgroup P := (Subgroup.center C).map C.subtype
  let O : Subgroup P := (omega₁ (Subgroup.center P) (p := 2)).map (Subgroup.center P).subtype
  let M : Subgroup P := centralizer (Z : Set P)
  have hOleZ : O ≤ Z := by
    intro y hy
    have hycenter : y ∈ Subgroup.center P :=
      map_subtype_le _ hy
    have hyomega : y ∈ (omega₁ C (p := 2)).map C.subtype := by
      rw [hC.omega_one_map_eq_center hno hZ]
      exact hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hyomega
    have hxC : (x : P) ∈ C := x.property
    refine Subgroup.mem_map_of_mem C.subtype ?_
    apply mem_center_iff.mpr
    intro c
    exact Subtype.ext (mem_center_iff.mp hycenter (c : P))
  have hZleC : Z ≤ C := map_subtype_le _
  have hZnormal : Z.Normal := by
    apply commutator_top_left_le_iff.mp
    exact (commutator_mono le_top hZleC).trans hC.commutator_le
  have hCsubM : C ≤ M := by
    apply le_centralizer_iff.mpr
    intro z hz c hc
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
    simpa using congrArg C.subtype (mem_center_iff.mp hw ⟨c, hc⟩)
  have hgenP : R.map C.subtype ⊔ Z = C := by
    rw [← R.map_sup, hRgen]
    ext x
    constructor
    · intro hx
      obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, by simp, rfl⟩
  have hMRleO : ⁅M, C⁆ ≤ O := by
    apply Subgroup.commutator_le.mpr
    intro m hm c hc
    obtain ⟨r, hr, z, hz, rfl⟩ := mem_sup_of_normal_right.mp
      (show c ∈ R.map C.subtype ⊔ Z from hgenP.symm ▸ hc)
    have hr4 : r ^ 4 = 1 := by
      obtain ⟨r', hr', hr'eq⟩ := Subgroup.mem_map.mp hr
      let rr : R := ⟨r', hr'⟩
      have he : rr ^ 4 = 1 := by
        have hev : (eR rr) ^ 4 = 1 := by
          rcases eR rr with i | i
          · fin_cases i <;> decide
          · simp only [QuaternionGroup.xa_pow_four]
        apply eR.injective
        simpa using hev
      have heC : (r' : C) ^ 4 = 1 := by
        simpa [rr] using congrArg (fun x : R => (x : C)) he
      have hpoly := congrArg C.subtype heC
      calc
        r ^ 4 = (C.subtype r') ^ 4 := by rw [hr'eq]
        _ = 1 := hpoly
    have hmr := commutator_mem_omega_center_of_fourth_power_eq_one hC
      hno hZ m r (map_subtype_le _ hr) hr4
    have hmz : Commute m z := ((mem_centralizer_iff.mp hm) z hz).symm
    have hid : ⁅m, r * z⁆ = ⁅m, r⁆ := by
      simp only [commutatorElement_def, mul_inv_rev]
      simp only [mul_assoc]
      rw [← mul_assoc z (m : P)⁻¹,
        show z * (m : P)⁻¹ = (m : P)⁻¹ * z from (hmz.inv_left.eq).symm]
      simp
    rw [hid]
    exact hmr
  have hMZ : ⁅M, Z⁆ = ⊥ := by
    apply bot_unique
    apply Subgroup.commutator_le.mpr
    intro m hm z hz
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      ((mem_centralizer_iff.mp hm) z hz).symm
  have hMCcentral : ⁅M, C⁆ ≤ center P := by
    exact hMRleO.trans (map_subtype_le _)
  have hPMcomm : ⁅(⊤ : Subgroup P), M⁆ ≤ Z := by
    have h₁ : ⁅⁅M, C⁆, (⊤ : Subgroup P)⁆ = ⊥ := by
      apply le_antisymm
      · exact (commutator_mono hMCcentral le_top).trans
          (commutator_center_left (⊤ : Subgroup P)).le
      · exact bot_le
    have h₂' : ⁅⁅(⊤ : Subgroup P), C⁆, M⁆ = ⊥ := by
      apply le_antisymm
      · have hzM : ⁅Z, M⁆ = ⊥ := by
          rw [← Subgroup.commutator_comm M Z]
          exact hMZ
        have hcZ : ⁅(⊤ : Subgroup P), C⁆ ≤ Z := by
          simpa [Z] using hC.commutator_le
        exact (commutator_mono hcZ le_rfl).trans hzM.le
      · exact bot_le
    have h₂ : ⁅⁅C, (⊤ : Subgroup P)⁆, M⁆ = ⊥ := by
      rw [Subgroup.commutator_comm C (⊤ : Subgroup P)]
      exact h₂'
    have hthree : ⁅⁅(⊤ : Subgroup P), M⁆, C⁆ = ⊥ :=
      Subgroup.commutator_commutator_eq_bot_of_rotate h₁ h₂
    intro x hx
    have hc := (commutator_eq_bot_iff_le_centralizer.mp hthree) hx
    rw [hC.centralizer_eq] at hc
    exact hc
  have hMnormalZ : M ≤ normalizer (Z : Set P) := by
    rw [le_normalizer_iff_commutator_le_right]
    exact hMZ.le.trans bot_le
  have hMcenter : Z ≤ centralizer (M : Set P) := by
    intro z hz m hm
    exact ((mem_centralizer_iff.mp hm) z hz).symm
  have hMsquareZ (m : M) : (m : P) ^ 2 ∈ Z := by
    change (m : P) ^ 2 ∈ (Subgroup.center C).map C.subtype
    rw [← hC.centralizer_eq]
    intro c hc
    let q : P := ⁅(m : P), c⁆
    have hq : q ∈ O := hMRleO (commutator_mem_commutator m.property hc)
    have hq2 : q ^ 2 = 1 := by
      let : IsElementaryAbelian 2 (omega₁ (Subgroup.center P) (p := 2)) :=
        IsElementaryAbelian.omega₁_of_isMulCommutative _
      let : IsElementaryAbelian 2 O := IsElementaryAbelian.map_subtype
      simpa [q] using elemPow_eq_one_of_isElementaryAbelian q hq
    have hqc : Commute q c := (mem_center_iff.mp (map_subtype_le _ hq) c).symm
    have hqm : Commute q (m : P) :=
      (hMcenter (hOleZ hq) (m : P) m.property).symm
    have hmc : (m : P) * c * (m : P)⁻¹ = q * c := by
      simp [q, commutatorElement_def, mul_assoc]
    have hsq : (m : P) ^ 2 * c * ((m : P) ^ 2)⁻¹ = c := by
      rw [pow_two]
      calc
        (m : P) * m * c * ((m : P) * m)⁻¹ =
            (m : P) * ((m : P) * c * (m : P)⁻¹) * (m : P)⁻¹ := by group
        _ = (m : P) * (q * c) * (m : P)⁻¹ := by rw [hmc]
        _ = q * ((m : P) * c * (m : P)⁻¹) := by
          rw [← mul_assoc (m : P) q c, show (m : P) * q = q * (m : P) from hqm.eq.symm]
          group
        _ = q * (q * c) := by rw [hmc]
        _ = c := by
          calc
            q * (q * c) = (q ^ 2) * c := by rw [pow_two, mul_assoc]
            _ = c := by rw [hq2, one_mul]
    exact (mul_inv_eq_iff_eq_mul.mp hsq).symm
  have hZleM : Z ≤ M := hZleC.trans hCsubM
  have hcenter : (center M).map M.subtype = Z := by
    rw [map_center_subtype_eq_inf_centralizer]
    apply le_antisymm
    · exact inf_le_right.trans ((centralizer_le hCsubM).trans hC.centralizer_eq.le)
    · exact le_inf hZleM hMcenter
  have hMquot : IsElementaryAbelian 2 (M ⧸ center M) := by
    have hs (q : M ⧸ center M) : q ^ 2 = 1 := by
      obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (center M) q
      rw [← map_pow]
      apply (QuotientGroup.eq_one_iff _).mpr
      have hm : ((m ^ 2 : M) : P) ∈ (center M).map M.subtype :=
        hcenter.symm ▸ hMsquareZ m
      obtain ⟨z, hz, he⟩ := hm
      exact (Subtype.ext he : z = m ^ 2) ▸ hz
    exact {
      toIsMulCommutative := ⟨⟨fun x y =>
        (Commute.of_orderOf_dvd_two (fun q => orderOf_dvd_of_pow_eq_one (hs q)) x y).eq⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
  let : C.Characteristic := hC.characteristic
  have hZchar : Z.Characteristic := by
    change ((center C).map C.subtype).Characteristic
    infer_instance
  let : Z.Characteristic := hZchar
  have hMchar : M.Characteristic := inferInstance
  have hcentM : centralizer (M : Set P) = Z :=
    le_antisymm ((centralizer_le hCsubM).trans hC.centralizer_eq.le) hMcenter
  exact ⟨⟨hMchar, hMquot, hcenter.symm ▸ hPMcomm, hcentM.trans hcenter.symm⟩,
    hcenter⟩

/-- The centralizer of the critical center contains the critical subgroup
with relative index at most two when that center is nonelementary. -/
public theorem relIndex_center_centralizer_le_two_of_quaternion_supplement
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    {C : Subgroup P} (hC : IsCriticalPSubgroup 2 C)
    (hnonab : ¬ IsMulCommutative C)
    (hbad : ¬ IsElementaryAbelian 2 (center C))
    (R : Subgroup C) (eR : R ≃* QuaternionGroup 2)
    (hRgen : R ⊔ center C = ⊤) :
    C.relIndex (centralizer ((center C).map C.subtype : Set P)) ≤ 2 := by
  let Z := (center C).map C.subtype
  let M := centralizer (Z : Set P)
  obtain ⟨hM, hcenter⟩ :=
    hC.center_centralizer_isCritical_of_quaternion_supplement hno hZ R eR hRgen
  change IsCriticalPSubgroup 2 M at hM
  change (center M).map M.subtype = Z at hcenter
  have hCM : C ≤ M := by
    apply le_centralizer_iff.mpr
    rw [show Z = C ⊓ centralizer (C : Set P) from map_center_subtype_eq_inf_centralizer C]
    exact inf_le_right
  have hbadM : ¬ IsElementaryAbelian 2 (center M) := by
    intro he
    let : IsElementaryAbelian 2 (center M) := he
    apply hbad
    refine { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
    intro z
    have hz : ((z : C) : P) ∈ (center M).map M.subtype :=
      hcenter.symm ▸ mem_map_of_mem C.subtype z.property
    obtain ⟨m, hm, hme⟩ := hz
    have hp := elemPow_eq_one_of_isElementaryAbelian (p := 2) m hm
    apply Subtype.ext
    apply Subtype.ext
    change ((z : C) : P) ^ 2 = 1
    simpa only [map_pow, map_one, hme] using congrArg M.subtype hp
  have hb := (hP.to_subgroup M).card_center_quotient_le_eight_of_nonelementary_center
    hM.quotient_elementary (hM.square_one_mem_center hno hZ)
    (hM.card_involutions_eq_three hno hZ) hbadM
  have hZM : Z.subgroupOf M = center M := by
    ext m
    constructor
    · intro hm
      have hm' : (m : P) ∈ (center M).map M.subtype := hcenter.symm ▸ hm
      obtain ⟨z, hz, he⟩ := hm'
      exact (Subtype.ext he : z = m) ▸ hz
    · intro hm
      exact hcenter ▸ mem_map_of_mem M.subtype hm
  have hZC : Z.subgroupOf C = center C := by
    ext c
    constructor
    · rintro ⟨z, hz, he⟩
      exact (Subtype.ext he : z = c) ▸ hz
    · intro hc
      exact mem_map_of_mem C.subtype hc
  have hfour : 4 ≤ Nat.card (C ⧸ center C) := by
    obtain ⟨n, hn⟩ := ((hP.to_subgroup C).to_quotient (center C)).exists_card_eq
    have hn2 : 2 ≤ n := by
      by_contra hh
      have hdvd : Nat.card (C ⧸ center C) ∣ 2 := by
        rw [hn]
        have : n ≤ 1 := by omega
        interval_cases n <;> norm_num
      let : IsCyclic (C ⧸ center C) := isCyclic_of_card_dvd_prime (p := 2) hdvd
      exact hnonab (isMulCommutative_of_isCyclic_quotient_center_self C)
    rw [hn]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn2
  have hmul := Z.relIndex_mul_relIndex C M (map_subtype_le _) hCM
  have hZMcard : Z.relIndex M = Nat.card (M ⧸ center M) := by
    rw [relIndex, hZM, index_eq_card]
  have hZCcard : Z.relIndex C = Nat.card (C ⧸ center C) := by
    rw [relIndex, hZC, index_eq_card]
  rw [hZMcard, hZCcard] at hmul
  change C.relIndex M ≤ 2
  nlinarith

end IsCriticalPSubgroup
