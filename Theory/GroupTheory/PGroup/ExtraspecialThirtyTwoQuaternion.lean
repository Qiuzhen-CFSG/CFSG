module

public import Theory.GroupTheory.PGroup.ExtraspecialThirtyTwoElementaryAlternative
public import Theory.GroupTheory.PGroup.DihedralCentralFactor
public import Theory.GroupTheory.HyperbolicQuaternionFactors

/-!
# Quaternion factors from an elementary eight in an extraspecial group of order 32

Split off a dihedral factor containing a noncentral involution of the given
elementary eight. An elementary element outside its central four projects to
a noncentral involution in the factor's centralizer. That centralizer has
order eight and center of order two, so splitting off another dihedral factor
identifies it with a dihedral eight. Reflection generators in the two factors
have the same central commutator and give the hyperbolic presentation used by
`exists_quaternion_factors_of_hyperbolic_involutions`.

This proves the quaternion–quaternion structure directly from a single
elementary eight; no generating second elementary eight is assumed.

Source: Janko–Thompson (1970), §4, printed p.390; the dihedral splitting
uses the intrinsic extraspecial results in `ExtraspecialInvolution`.
-/

open Subgroup
open scoped commutatorElement


private theorem dihedral_commuting_involution_cases :
    ∀ t d : DihedralGroup 4, t ^ 2 = 1 → t ≠ 1 → t ≠ DihedralGroup.r 2 →
      d * t = t * d → d = 1 ∨ d = t ∨ d = DihedralGroup.r 2 ∨
        d = DihedralGroup.r 2 * t := by
  exact (by decide +kernel)

private theorem rotation_of_noncentral_involution_mem
    {P : Type*} [Group P] [IsExtraspecial 2 P]
    (t : P) (ht : t ^ 2 = 1) (htZ : t ∉ center P) :
    ∃ a : P, orderOf a = 4 ∧ t * a * t⁻¹ = a⁻¹ := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ht)
  obtain ⟨y, hy⟩ : ∃ y : P, y * t ≠ t * y := by
    simpa only [mem_center_iff, not_forall] using htZ
  have horder {a : P} (ha : a ^ 2 ≠ 1) : orderOf a = 4 := by
    exact orderOf_eq_prime_pow (p := 2) (n := 1) ha (IsExtraspecial.pow_four_eq_one a)
  by_cases hy2 : y ^ 2 = 1
  · have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hy2)
    refine ⟨y * t, horder ?_, ?_⟩
    · intro he
      have hi : (y * t)⁻¹ = y * t := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using he)
      simp only [mul_inv_rev, hti, hyi] at hi
      exact hy hi.symm
    · simp only [mul_inv_rev, hti, hyi, mul_assoc]
      rw [← pow_two, ht, mul_one]
  · have hc : ⁅t, y⁆ ∈ center P :=
      (IsExtraspecial.quotient_elementary_abelian 2 P).commutator_le_center_of_central_quotient
        (commutator_mem_commutator (mem_top t) (mem_top y))
    have hcne : ⁅t, y⁆ ≠ 1 := fun h => hy
      (commutatorElement_eq_one_iff_mul_comm.mp h).symm
    obtain ⟨z, _, hz⟩ := (Nat.card_eq_two_iff' (1 : center P)).mp
      (IsExtraspecial.center_order_p 2 P)
    have hceq : ⁅t, y⁆ = y ^ 2 := congrArg Subtype.val
      ((hz ⟨⁅t, y⁆, hc⟩ (fun h => hcne (congrArg Subtype.val h))).trans
        (hz ⟨y ^ 2, IsExtraspecial.square_mem_center y⟩
          (fun h => hy2 (congrArg Subtype.val h))).symm)
    refine ⟨y, horder hy2, ?_⟩
    calc
      t * y * t⁻¹ = ⁅t, y⁆ * y := by
        simp only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one]
      _ = y ^ 2 * y := by rw [hceq]
      _ = y⁻¹ := by
        apply mul_right_cancel (b := y)
        simpa only [pow_succ, pow_zero, one_mul, inv_mul_cancel] using
          IsExtraspecial.pow_four_eq_one y

private theorem exists_dihedral_factor_of_noncentral_involution_mem
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P]
    (t : P) (ht : t ^ 2 = 1) (htZ : t ∉ center P) :
    ∃ D : Subgroup P, Nonempty (D ≃* DihedralGroup 4) ∧ center P ≤ D ∧
      D ⊔ centralizer (D : Set P) = ⊤ ∧ t ∈ D := by
  obtain ⟨a, ha, hinv⟩ := rotation_of_noncentral_involution_mem t ht htZ
  have ha2 : a ^ 2 ≠ 1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [ha] at hd
    norm_num at hd
  have htout : t ∉ zpowers a := by
    intro h
    have hc : Commute t a := by
      obtain ⟨k, rfl⟩ := h
      exact (Commute.refl a).zpow_left k
    have he : a = a⁻¹ := by simpa only [hc.eq, mul_inv_cancel_right] using hinv
    apply ha2
    simpa only [pow_two] using (congrArg (fun x : P => x * a) he).trans (inv_mul_cancel a)
  have hn : t ∈ normalizer (zpowers a : Set P) := by
    rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change zpowers (t * a * t⁻¹) = zpowers a
    rw [hinv, zpowers_inv]
  let D := zpowers a ⊔ zpowers t
  have hcard : Nat.card D = 8 := by
    rw [card_sup_zpowers_of_normalizing_involution (zpowers a) t ht htout hn,
      Nat.card_zpowers, ha]
  have haD : a ∈ D := mem_sup_left (mem_zpowers a)
  have htD : t ∈ D := mem_sup_right (mem_zpowers t)
  let aD : D := ⟨a, haD⟩
  let tD : D := ⟨t, htD⟩
  have hgen : closure ({aD, tD} : Set D) = ⊤ := by
    apply map_injective D.subtype_injective
    rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
      ← MonoidHom.range_eq_map, D.range_subtype]
    change closure ({a, t} : Set P) = zpowers a ⊔ zpowers t
    rw [← Set.singleton_union, Subgroup.closure_union, ← zpowers_eq_closure, ← zpowers_eq_closure]
  have hmodel : Nonempty (D ≃* DihedralGroup 4) :=
    dihedralGroup_equiv_of_presentation (by decide) aD tD
      ((Subgroup.orderOf_coe aD).symm.trans ha)
      (Subtype.ext ht) (Subtype.ext hinv) hgen hcard
  have hZD : center P ≤ D := by
    have heq : zpowers (a ^ 2) = center P := by
      apply eq_of_le_of_card_ge (zpowers_le.mpr (IsExtraspecial.square_mem_center a))
      rw [Nat.card_zpowers, orderOf_pow, ha, IsExtraspecial.center_order_p 2 P]
      decide
    rw [← heq]
    exact zpowers_le.mpr (D.pow_mem haD 2)
  have hnonab : ¬ IsMulCommutative D := by
    intro h
    let : IsMulCommutative D := h
    have he : a = a⁻¹ := by
      have hcomm : t * a = a * t := congrArg Subtype.val (mul_comm' tD aD)
      simpa only [hcomm, mul_inv_cancel_right] using hinv
    exact ha2 (by simpa only [pow_two] using
      (congrArg (fun x : P => x * a) he).trans (inv_mul_cancel a))
  have hcenter : Nat.card (center D) = 2 :=
    card_center_eq_prime_of_card_eq_prime_cube (p := 2) hcard hnonab
  have himage : (center D).map D.subtype = center P := by
    apply (eq_of_le_of_card_ge ?_ ?_).symm
    · intro x hx
      refine ⟨⟨x, hZD hx⟩, ?_, rfl⟩
      exact mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp hx y))
    · rw [card_map_of_injective D.subtype_injective, hcenter,
        IsExtraspecial.center_order_p 2 P]
  let : IsExtraspecial 2 D := {
    center_order_p := hcenter
    quotient_elementary_abelian :=
      (IsExtraspecial.quotient_elementary_abelian 2 P).central_quotient_subgroup D
    quotient_nontrivial := QuotientGroup.nontrivial_iff.mpr
      (fun h => hnonab (center_eq_top_iff.mp h)) }
  refine ⟨D, hmodel, hZD, sup_centralizer_eq_top_of_extraspecial_two D ?_, htD⟩
  rw [himage]
  exact (commutator_mono le_rfl le_top).trans
    (IsExtraspecial.quotient_elementary_abelian 2 P).commutator_le_center_of_central_quotient

private theorem dihedral_reflections
    {P : Type*} [Group P] (D : Subgroup P) (e : D ≃* DihedralGroup 4) :
    ∃ x y : P, x ∈ D ∧ y ∈ D ∧ x ^ 2 = 1 ∧ y ^ 2 = 1 ∧
      ⁅x,y⁆ ≠ 1 ∧ ⁅x,y⁆ ∈ (center D).map D.subtype ∧
      closure ({x,y} : Set P) = D := by
  let x : D := e.symm (DihedralGroup.sr 0)
  let y : D := e.symm (DihedralGroup.sr 1)
  have hx : x ^ 2 = 1 := by apply e.injective; simp [x]; decide
  have hy : y ^ 2 = 1 := by apply e.injective; simp [y]; decide
  have hcomm : ⁅x,y⁆ ≠ 1 := by
    intro h
    have hh := congrArg e h
    simp only [map_commutatorElement, x, y, e.apply_symm_apply, map_one] at hh
    exact (by decide : ⁅DihedralGroup.sr 0, DihedralGroup.sr 1⁆ ≠ (1 : DihedralGroup 4)) hh
  have hc : ⁅x,y⁆ ∈ center D := by
    apply mem_center_iff.mpr
    intro d
    apply e.injective
    simp only [map_mul, map_commutatorElement, x, y, e.apply_symm_apply]
    exact (by decide : ∀ d : DihedralGroup 4,
      d * ⁅DihedralGroup.sr 0, DihedralGroup.sr 1⁆ =
        ⁅DihedralGroup.sr 0, DihedralGroup.sr 1⁆ * d) (e d)
  refine ⟨x, y, x.property, y.property, congrArg Subtype.val hx,
    congrArg Subtype.val hy, ?_, ?_, ?_⟩
  · exact fun h => hcomm (Subtype.ext h)
  · exact mem_map_of_mem D.subtype hc
  · apply le_antisymm ((closure_le _).mpr (by
      intro a ha
      rcases (show a = (x : P) ∨ a = (y : P) by simpa using ha) with rfl | rfl
      · exact x.property
      · exact y.property))
    intro d hd
    have hwords : ∀ d : DihedralGroup 4,
        d = 1 ∨ d = DihedralGroup.sr 0 ∨ d = DihedralGroup.sr 1 ∨
        d = DihedralGroup.sr 0 * DihedralGroup.sr 1 ∨
        d = DihedralGroup.sr 1 * DihedralGroup.sr 0 ∨
        d = DihedralGroup.sr 0 * DihedralGroup.sr 1 * DihedralGroup.sr 0 ∨
        d = DihedralGroup.sr 1 * DihedralGroup.sr 0 * DihedralGroup.sr 1 ∨
        d = DihedralGroup.sr 0 * DihedralGroup.sr 1 *
          DihedralGroup.sr 0 * DihedralGroup.sr 1 := by decide
    have hw := hwords (e ⟨d, hd⟩)
    have hwords' : (⟨d,hd⟩ : D) = 1 ∨ (⟨d,hd⟩ : D) = x ∨ (⟨d,hd⟩ : D) = y ∨
        (⟨d,hd⟩ : D) = x*y ∨ (⟨d,hd⟩ : D) = y*x ∨
        (⟨d,hd⟩ : D) = x*y*x ∨ (⟨d,hd⟩ : D) = y*x*y ∨
        (⟨d,hd⟩ : D) = x*y*x*y := by
      simpa only [map_mul, map_one, x, y, e.symm_apply_apply]
        using hw.imp (fun h => congrArg e.symm h)
          (fun h => h.imp (fun h => congrArg e.symm h)
            (fun h => h.imp (fun h => congrArg e.symm h)
              (fun h => h.imp (fun h => congrArg e.symm h)
                (fun h => h.imp (fun h => congrArg e.symm h)
                  (fun h => h.imp (fun h => congrArg e.symm h)
                    (fun h => h.imp (fun h => congrArg e.symm h)
                      (fun h => congrArg e.symm h)))))))
    let T := closure ({(x : P), (y : P)} : Set P)
    have hxT : (x : P) ∈ T := subset_closure (by simp)
    have hyT : (y : P) ∈ T := subset_closure (by simp)
    rcases hwords' with h | h | h | h | h | h | h | h
    all_goals have hh := congrArg Subtype.val h
    all_goals change d = _ at hh
    all_goals rw [hh]
    · simpa only [OneMemClass.coe_one] using T.one_mem
    · simpa only [] using hxT
    · simpa only [] using hyT
    · simpa only [coe_mul] using T.mul_mem hxT hyT
    · simpa only [coe_mul] using T.mul_mem hyT hxT
    · simpa only [coe_mul] using T.mul_mem (T.mul_mem hxT hyT) hxT
    · simpa only [coe_mul] using T.mul_mem (T.mul_mem hyT hxT) hyT
    · simpa only [coe_mul] using T.mul_mem (T.mul_mem (T.mul_mem hxT hyT) hxT) hyT

/-- An elementary eight in an extraspecial group of order 32 determines the
quaternion–quaternion central-product type. -/
public theorem exists_quaternion_factors_of_extraspecial_thirty_two_elementary
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P]
    (hP : Nat.card P = 32) (E : Subgroup P) [E.Normal]
    [IsElementaryAbelian 2 E] (hE : Nat.card E = 8)
    (hZE : center P ≤ E) :
    ∃ B C : Subgroup P, Nonempty (B ≃* QuaternionGroup 2) ∧
      Nonempty (C ≃* QuaternionGroup 2) ∧ B ⊔ C = ⊤ ∧
      Nat.card (B ⊓ C : Subgroup P) = 2 ∧
      (∀ b ∈ B, ∀ c ∈ C, b * c = c * b) := by
  let : IsElementaryAbelian 2 (center P) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun z => by
      simpa only [IsExtraspecial.center_order_p 2 P] using (pow_card_eq_one' (x := z)) }
  have hnot : ¬ E ≤ center P := by
    intro h
    have hc := card_le_of_le h
    rw [hE, IsExtraspecial.center_order_p 2 P] at hc
    omega
  obtain ⟨t, htE, htZ⟩ := SetLike.not_le_iff_exists.mp hnot
  have ht2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) t htE
  obtain ⟨D, ⟨eD⟩, hZD, hgenD, htD⟩ :=
    exists_dihedral_factor_of_noncentral_involution_mem t ht2 htZ
  let C0 := centralizer (D : Set P)
  have hDcard : Nat.card D = 8 := by
    rw [Nat.card_congr eD.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
  have hCcard : Nat.card C0 = 8 := by
    have hh := card_eq_four_mul_card_centralizer_of_dihedral_factor D eD hgenD
    change Nat.card (centralizer (D : Set P)) = 8
    rw [hP] at hh
    omega
  let : D.Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [← hgenD]
    exact sup_le D.le_normalizer (centralizer_le_normalizer _)))
  have hcenterD_to_P : ∀ x : D, x ∈ center D → (x : P) ∈ center P := by
    intro x hx
    rw [mem_center_iff]
    intro g
    obtain ⟨d, hd, c, hc, rfl⟩ := mem_sup_of_normal_left.mp (hgenD ▸ mem_top g)
    have hxd : (x : P) * d = d * (x : P) :=
      (congrArg Subtype.val (mem_center_iff.mp hx ⟨d, hd⟩)).symm
    have hxc : (x : P) * c = c * (x : P) := hc (x : P) x.property
    calc
      (d * c) * (x : P) = d * (c * (x : P)) := by rw [mul_assoc]
      _ = d * ((x : P) * c) := by rw [hxc]
      _ = (d * (x : P)) * c := by rw [← mul_assoc]
      _ = ((x : P) * d) * c := by rw [hxd]
      _ = (x : P) * (d * c) := by rw [mul_assoc]
  let F := center P ⊔ zpowers t
  have hFleD : F ≤ D := sup_le hZD (zpowers_le.mpr htD)
  have hFleE : F ≤ E := sup_le hZE (zpowers_le.mpr htE)
  have hFcard : Nat.card F = 4 := by
    rw [card_sup_zpowers_of_normalizing_involution (center P) t ht2 htZ
      (by rw [normalizer_eq_top]; exact mem_top t), IsExtraspecial.center_order_p 2 P]
  obtain ⟨u, huE, huF⟩ : ∃ u ∈ E, u ∉ F := by
    by_contra! hh
    have hle : E ≤ F := fun x hx => by exact hh x hx
    have hc := card_le_of_le hle
    rw [hE, hFcard] at hc
    omega
  obtain ⟨d, hdD, c, hcC, hduc⟩ := mem_sup_of_normal_left.mp (hgenD ▸ mem_top u)
  have htu : Commute u t := by
    exact congrArg Subtype.val (mul_comm' (⟨u, huE⟩ : E) ⟨t, htE⟩)
  have hdt : d * t = t * d := by
    apply mul_right_cancel (b := c)
    calc
      (d * t) * c = d * (c * t) := by rw [mul_assoc, hcC t htD]
      _ = (d * c) * t := by rw [← mul_assoc]
      _ = u * t := by rw [hduc]
      _ = t * u := htu.eq
      _ = t * (d * c) := by rw [hduc]
      _ = (t * d) * c := by rw [mul_assoc]
  have hdF : d ∈ F := by
    let tD' : D := ⟨t, htD⟩
    have htD1 : eD tD' ≠ 1 := by
      intro h
      have hteq : t = 1 := congrArg Subtype.val (eD.injective (h.trans (eD.map_one).symm))
      apply htZ
      rw [hteq]
      exact (center P).one_mem
    have htDr : eD tD' ≠ DihedralGroup.r 2 := by
      intro h
      have hcent : tD' ∈ center D := by
        rw [mem_center_iff]
        intro x
        apply eD.injective
        rw [map_mul, map_mul, h]
        exact (by decide : ∀ y : DihedralGroup 4,
          y * (DihedralGroup.r 2) = (DihedralGroup.r 2) * y) (eD x)
      exact htZ (hcenterD_to_P tD' hcent)
    have hcomm' : eD ⟨d, hdD⟩ * eD tD' = eD tD' * eD ⟨d, hdD⟩ := by
      have hdtD : (⟨d, hdD⟩ : D) * tD' = tD' * ⟨d, hdD⟩ := Subtype.ext hdt
      simpa only [map_mul] using congrArg (fun q : D => eD q) hdtD
    rcases dihedral_commuting_involution_cases (eD tD') (eD ⟨d, hdD⟩)
      (by have ht2D : tD' ^ 2 = 1 := Subtype.ext ht2
          simpa only [map_pow, map_one] using congrArg eD ht2D) htD1 htDr hcomm' with h | h | h | h
    · have hh : (⟨d, hdD⟩ : D) = 1 := eD.injective (h.trans (eD.map_one).symm)
      rw [show d = 1 from congrArg Subtype.val hh]
      exact F.one_mem
    · have hh : (⟨d, hdD⟩ : D) = tD' := eD.injective h
      rw [show d = t from congrArg Subtype.val hh]
      exact mem_sup_right (mem_zpowers t)
    · have hr2D : eD.symm (DihedralGroup.r 2) ∈ center D := by
        rw [mem_center_iff]
        intro x
        apply eD.injective
        rw [map_mul, map_mul, eD.apply_symm_apply]
        exact (by decide : ∀ y : DihedralGroup 4,
          y * (DihedralGroup.r 2) = (DihedralGroup.r 2) * y) (eD x)
      have hr2P : (eD.symm (DihedralGroup.r 2) : P) ∈ center P :=
        hcenterD_to_P _ hr2D
      have hh : (⟨d, hdD⟩ : D) = eD.symm (DihedralGroup.r 2) :=
        eD.injective (h.trans (eD.apply_symm_apply _).symm)
      rw [show d = (eD.symm (DihedralGroup.r 2) : P) from congrArg Subtype.val hh]
      exact mem_sup_left hr2P
    · have hr2D : eD.symm (DihedralGroup.r 2) ∈ center D := by
        rw [mem_center_iff]
        intro x
        apply eD.injective
        rw [map_mul, map_mul, eD.apply_symm_apply]
        exact (by decide : ∀ y : DihedralGroup 4,
          y * (DihedralGroup.r 2) = (DihedralGroup.r 2) * y) (eD x)
      have hr2P : (eD.symm (DihedralGroup.r 2) : P) ∈ center P :=
        hcenterD_to_P _ hr2D
      have hh : (⟨d, hdD⟩ : D) = eD.symm (DihedralGroup.r 2 * eD tD') :=
        eD.injective (h.trans (eD.apply_symm_apply _).symm)
      have hh' : d = (eD.symm (DihedralGroup.r 2) : P) * t := by
        rw [show d = (eD.symm (DihedralGroup.r 2 * eD tD') : P) from congrArg Subtype.val hh]
        rw [map_mul, eD.symm_apply_apply]
        rfl
      rw [hh']
      exact F.mul_mem (mem_sup_left hr2P) (mem_sup_right (mem_zpowers t))
  have hcuE : c ∈ E := by
    have hc_eq : c = d⁻¹ * u := by calc
      c = d⁻¹ * (d * c) := by group
      _ = d⁻¹ * u := by rw [hduc]
    rw [hc_eq]
    exact E.mul_mem (E.inv_mem (hFleE hdF)) huE
  have hcneZ : c ∉ center P := by
    intro hcZ
    apply huF
    have hu_eq : u = d * c := hduc.symm
    rw [hu_eq]
    exact F.mul_mem hdF (mem_sup_left hcZ)
  have hc2 : c ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) c hcuE
  have hcenterC_to_P : ∀ x : C0, x ∈ center C0 → (x : P) ∈ center P := by
    intro x hx
    apply mem_center_iff.mpr
    intro g
    have hle : D ⊔ C0 ≤ centralizer ({(x : P)} : Set P) := by
      apply sup_le
      · intro d hd
        exact mem_centralizer_singleton_iff.mpr (x.property d hd)
      · intro d hd
        exact mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_center_iff.mp hx ⟨d, hd⟩))
    rw [hgenD] at hle
    exact mem_centralizer_singleton_iff.mp (hle (mem_top g))
  have hcenterC : (center C0).map C0.subtype = center P := by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact hcenterC_to_P y hy
    · intro x hx
      refine ⟨⟨x, center_le_centralizer _ hx⟩, ?_, rfl⟩
      exact mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp hx y))
  have hZCcard : Nat.card (center C0) = 2 := by
    rw [← card_map_of_injective C0.subtype_injective, hcenterC,
      IsExtraspecial.center_order_p 2 P]
  let : IsExtraspecial 2 C0 := {
    center_order_p := hZCcard
    quotient_elementary_abelian :=
      (IsExtraspecial.quotient_elementary_abelian 2 P).central_quotient_subgroup C0
    quotient_nontrivial := QuotientGroup.nontrivial_iff.mpr (by
      intro h
      have hh : Nat.card (center C0) = Nat.card C0 := by
        rw [h, Nat.card_congr topEquiv.toEquiv]
      omega) }
  have hcnot : (⟨c, hcC⟩ : C0) ∉ center C0 := fun h =>
    hcneZ (hcenterC_to_P _ h)
  obtain ⟨D2, ⟨e2⟩, _, _⟩ :=
    IsExtraspecial.exists_dihedral_factor_of_noncentral_involution
      (⟨c, hcC⟩ : C0) (Subtype.ext hc2) hcnot
  have hD2 : D2 = ⊤ := D2.eq_top_of_card_eq (by
    rw [Nat.card_congr e2.toEquiv, DihedralGroup.nat_card, hCcard])
  have hmodelC : Nonempty (C0 ≃* DihedralGroup 4) := by
    subst D2
    exact ⟨topEquiv.symm.trans e2⟩
  obtain ⟨eC⟩ := hmodelC
  obtain ⟨x1,y1,hx1D,hy1D,hx1,hy1,hcomm1,hcent1,hgen1⟩ := dihedral_reflections D eD
  obtain ⟨x2,y2,hx2C,hy2C,hx2,hy2,hcomm2,hcent2,hgen2⟩ := dihedral_reflections C0 eC
  have hz1 : ⁅x1,y1⁆ ∈ center P := by
    obtain ⟨v, hv, he⟩ := hcent1
    exact he ▸ hcenterD_to_P v hv
  have hz2 : ⁅x2,y2⁆ ∈ center P := by
    rw [← hcenterC]
    exact hcent2
  have heq : ⁅x2,y2⁆ = ⁅x1,y1⁆ := by
    obtain ⟨z, _, hcases⟩ := (Nat.card_eq_two_iff' (1 : center P)).mp
      (IsExtraspecial.center_order_p 2 P)
    exact congrArg Subtype.val ((hcases ⟨_,hz2⟩ (fun h => hcomm2 (congrArg Subtype.val h))).trans
      (hcases ⟨_,hz1⟩ (fun h => hcomm1 (congrArg Subtype.val h))).symm)
  apply exists_quaternion_factors_of_hyperbolic_involutions x1 y1 x2 y2 ⁅x1,y1⁆
    hx1 hy1 hx2 hy2 hcomm1
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hz1) hz1 rfl heq
    (hx2C x1 hx1D) (hy2C x1 hx1D) (hx2C y1 hy1D) (hy2C y1 hy1D)
  have he : ({x1,y1,x2,y2} : Set P) = {x1,y1} ∪ {x2,y2} := by ext; simp; tauto
  rw [he, Subgroup.closure_union, hgen1, hgen2]
  exact hgenD
