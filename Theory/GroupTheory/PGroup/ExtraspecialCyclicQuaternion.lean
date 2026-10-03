module
public import Theory.GroupTheory.PGroup.ExtraspecialSmallOrder
public import Theory.GroupTheory.PGroup.ExtraspecialCentralProductOrder
public import Theory.GroupTheory.QuaternionGenerated

/-!
# A characteristic quaternion factor in an extraspecial–cyclic product

An extraspecial binary factor of order eight commuting with a cyclic tail
of order at least eight has a characteristic quaternion-eight supplement
to that tail. The given extraspecial factor need not be quaternion.

The existing central-product order API identifies the tail with the ambient
center. The small extraspecial classification leaves dihedral and quaternion
factors. In the dihedral case, multiply a reflection by a central element
of order four: together with a rotation this gives quaternion generators,
and their subgroup still supplements the center.

For characteristicity, a quaternion-eight supplement to a finite cyclic
center contains every ambient noncentral element of order four. Indeed,
write such an element as q*d with d central. Then q is noncentral in the
quaternion factor, and the nontrivial squares of q and q*d are the unique
involution in the center. Thus d has square one and belongs to the factor.
Automorphisms preserve noncentrality and order, so they preserve the two
standard quaternion generators and hence the factor. This avoids choosing
a dihedral factor invariant under automorphisms or treating central roots
of the involution as quaternion generators.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, Case 2, printed p.393
(PDF page 9), the characteristic quaternion subgroup of the second omega.
The proof is intrinsic and uses no recognition modules.
-/

open Subgroup
namespace Subgroup

private theorem cyclic_two_group_has_four
    {D : Type*} [Group D] [Finite D] [IsCyclic D]
    (hD : IsPGroup 2 D) (hcard : 4 ≤ Nat.card D) :
    ∃ c : D, orderOf c = 4 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := D)
  obtain ⟨n, hn⟩ := hD.exists_card_eq
  have hn2 : 2 ≤ n := by
    by_contra h
    have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl <;> simp_all
  have hdvd : 4 ∣ orderOf g := by
    rw [hg, hn]
    exact pow_dvd_pow 2 hn2
  exact ⟨g ^ (orderOf g / 4), orderOf_pow_orderOf_div
    (by rw [hg]; exact Nat.card_pos.ne') hdvd⟩

private theorem quaternion_supplement_of_dihedral
    {H : Type*} [Group H] [Finite H] [IsCyclic (center H)]
    (hH : IsPGroup 2 H) (B : Subgroup H)
    (e : B ≃* DihedralGroup 4) (hgen : B ⊔ center H = ⊤)
    (hcard : 4 ≤ Nat.card (center H)) :
    ∃ Q : Subgroup H, Nonempty (Q ≃* QuaternionGroup 2) ∧
      Q ⊔ center H = ⊤ := by
  let f : DihedralGroup 4 →* H := B.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := B.subtype_injective.comp e.symm.injective
  let a : H := f (DihedralGroup.r 1)
  let s : H := f (DihedralGroup.sr 0)
  let z : H := a ^ 2
  have ha4 : orderOf a = 4 := (orderOf_injective f hf _).trans
    DihedralGroup.orderOf_r_one
  have hz2 : orderOf z = 2 := by rw [orderOf_pow, ha4]; decide
  have hz1 : z ≠ 1 := by intro h; simp [h] at hz2
  have hzC : z ∈ center H := by
    have hB : B ≤ centralizer ({z} : Set H) := by
      intro b hb
      apply mem_centralizer_singleton_iff.mpr
      have hb' : f (e ⟨b, hb⟩) = b := by simp [f]
      rw [← hb']
      change f (e ⟨b, hb⟩) * f (DihedralGroup.r 1) ^ 2 =
        f (DihedralGroup.r 1) ^ 2 * f (e ⟨b, hb⟩)
      simp only [← map_pow, ← map_mul]
      apply congrArg f
      exact (by decide : ∀ b : DihedralGroup 4,
        b * (DihedralGroup.r 1) ^ 2 = (DihedralGroup.r 1) ^ 2 * b) _
    apply mem_center_iff.mpr
    intro x
    have ht : (⊤ : Subgroup H) ≤ centralizer ({z} : Set H) := by
      rw [← hgen]
      exact sup_le hB (center_le_centralizer _)
    exact mem_centralizer_singleton_iff.mp (ht (mem_top x))
  obtain ⟨c, hc⟩ := cyclic_two_group_has_four (hH.to_subgroup (center H)) hcard
  have hc2 : (c : H) ^ 2 = z := by
    refine congrArg (fun v : center H => (v : H))
      (IsCyclic.eq_of_orderOf_eq_two (x := c ^ 2)
        (y := (⟨z, hzC⟩ : center H)) ?_ ?_)
    · rw [orderOf_pow, hc]; decide
    · simpa only [← Subgroup.orderOf_coe] using hz2
  have hs2 : s ^ 2 = 1 := by
    change f (DihedralGroup.sr 0) ^ 2 = 1
    rw [← map_pow, show (DihedralGroup.sr 0 : DihedralGroup 4) ^ 2 = 1 by decide,
      map_one]
  let b : H := s * c
  have hb2 : b ^ 2 = a ^ 2 := by
    change (s * (c : H)) ^ 2 = a ^ 2
    rw [(show Commute s (c : H) from mem_center_iff.mp c.property s).mul_pow,
      hs2, one_mul, hc2]
  have hsinv : s * a * s⁻¹ = a⁻¹ := by
    change f (DihedralGroup.sr 0) * f (DihedralGroup.r 1) *
      (f (DihedralGroup.sr 0))⁻¹ = (f (DihedralGroup.r 1))⁻¹
    simp only [← map_mul, ← map_inv]
    exact congrArg f (by decide)
  have hbinv : b * a * b⁻¹ = a⁻¹ := by
    dsimp [b]
    rw [mul_inv_rev]
    calc
      s * c * a * ((c : H)⁻¹ * s⁻¹) =
          s * ((c : H) * a * (c : H)⁻¹) * s⁻¹ := by group
      _ = s * a * s⁻¹ := by
        rw [← mem_center_iff.mp c.property a]
        simp only [mul_assoc, mul_inv_cancel, mul_one]
      _ = a⁻¹ := hsinv
  have hbout : b ∉ zpowers a := by
    rintro ⟨i, hi⟩
    have hcomm : Commute b a := hi ▸ (Commute.refl a).zpow_left i
    have hfix : b * a * b⁻¹ = a := by
      rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
    apply hz1
    change a ^ 2 = 1
    calc
      a ^ 2 = a * a := pow_two _
      _ = a⁻¹ * a := congrArg (· * a) (hfix.symm.trans hbinv)
      _ = 1 := inv_mul_cancel _
  obtain ⟨_, hQ⟩ := QuaternionGroup.closure_equiv_of_relations
    (m := 2) (by decide) a b ha4 hb2 hbinv hbout
  let Q := closure ({a, b} : Set H)
  refine ⟨Q, hQ, ?_⟩
  have haQ : a ∈ Q := subset_closure (by simp)
  have hbQ : b ∈ Q := subset_closure (by simp)
  have hs : s ∈ Q ⊔ center H := by
    have hh := (Q ⊔ center H).mul_mem (mem_sup_left hbQ)
      (mem_sup_right ((center H).inv_mem c.property))
    simpa only [b, mul_inv_cancel_right] using hh
  apply top_unique
  rw [← hgen]
  refine sup_le ?_ le_sup_right
  intro x hx
  have hx' : f (e ⟨x, hx⟩) = x := by simp [f]
  rw [← hx']
  cases e ⟨x, hx⟩ with
  | r i =>
    have hi : (DihedralGroup.r i : DihedralGroup 4) = DihedralGroup.r 1 ^ i.val := by simp
    rw [hi, map_pow]
    exact (Q ⊔ center H).pow_mem (mem_sup_left haQ) _
  | sr i =>
    have hi : (DihedralGroup.sr i : DihedralGroup 4) =
        DihedralGroup.sr 0 * DihedralGroup.r 1 ^ i.val := by simp
    rw [hi, map_mul, map_pow]
    exact (Q ⊔ center H).mul_mem hs ((Q ⊔ center H).pow_mem (mem_sup_left haQ) _)

private theorem central_of_central_in_supplement
    {H : Type*} [Group H] (Q : Subgroup H)
    (hgen : Q ⊔ center H = ⊤) (q : Q) (hq : q ∈ center Q) :
    (q : H) ∈ center H := by
  apply mem_center_iff.mpr
  intro x
  have ht : (⊤ : Subgroup H) ≤ centralizer ({(q : H)} : Set H) := by
    rw [← hgen]
    refine sup_le ?_ (center_le_centralizer _)
    intro y hy
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp hq ⟨y, hy⟩))
  exact mem_centralizer_singleton_iff.mp (ht (mem_top x))

private theorem quaternion_supplement_contains_noncentral_four
    {H : Type*} [Group H] [Finite H] [IsCyclic (center H)]
    (Q : Subgroup H) (e : Q ≃* QuaternionGroup 2)
    (hgen : Q ⊔ center H = ⊤) (x : H)
    (hx : x ∉ center H) (hx4 : orderOf x = 4) : x ∈ Q := by
  obtain ⟨q, hq, d, hd, rfl⟩ := mem_sup_of_normal_right.mp
    (show x ∈ Q ⊔ center H by rw [hgen]; trivial)
  let qq : Q := ⟨q, hq⟩
  have hqn : qq ∉ center Q := by
    intro hh
    exact hx ((center H).mul_mem (central_of_central_in_supplement Q hgen qq hh) hd)
  have hq2C : qq ^ 2 ∈ center Q := by
    apply mem_center_iff.mpr
    intro t
    apply e.injective
    simp only [map_mul, map_pow]
    exact (by decide : ∀ a b : QuaternionGroup 2, b * a ^ 2 = a ^ 2 * b) _ _
  have hq2 : orderOf (qq ^ 2) = 2 := by
    have hh : ∀ a : QuaternionGroup 2,
        (∀ b : QuaternionGroup 2, b * a = a * b) ∨
          ((a ^ 2) ^ 2 = 1 ∧ a ^ 2 ≠ 1) := by decide
    rcases hh (e qq) with ha | ha
    · exact (hqn (mem_center_iff.mpr fun t => e.injective (by
        simpa only [map_mul] using ha (e t)))).elim
    · have he : orderOf ((e qq) ^ 2) = 2 := orderOf_eq_prime ha.1 ha.2
      simpa only [← map_pow, e.orderOf_eq] using he
  have hq2H : orderOf (q ^ 2) = 2 := (Subgroup.orderOf_coe (qq ^ 2)).trans hq2
  have hq2Z : q ^ 2 ∈ center H := central_of_central_in_supplement Q hgen (qq ^ 2) hq2C
  have hqd : Commute q d := mem_center_iff.mp hd q
  have hx2Z : (q * d) ^ 2 ∈ center H := by
    rw [hqd.mul_pow]
    exact (center H).mul_mem hq2Z ((center H).pow_mem hd 2)
  have hxeq : (q * d) ^ 2 = q ^ 2 := by
    refine congrArg (fun z : center H => (z : H))
      (IsCyclic.eq_of_orderOf_eq_two
        (x := ⟨(q * d) ^ 2, hx2Z⟩) (y := ⟨q ^ 2, hq2Z⟩) ?_ ?_)
    · rw [← Subgroup.orderOf_coe, orderOf_pow, hx4]; decide
    · rw [← Subgroup.orderOf_coe]; exact hq2H
  have hd2 : d ^ 2 = 1 := by
    rw [hqd.mul_pow] at hxeq
    exact mul_left_cancel (hxeq.trans (mul_one (q ^ 2)).symm)
  have hdQ : d ∈ Q := by
    by_cases hd1 : d = 1
    · simpa only [hd1] using Q.one_mem
    have hdeq : d = q ^ 2 := by
      refine congrArg (fun z : center H => (z : H))
        (IsCyclic.eq_of_orderOf_eq_two
          (x := ⟨d, hd⟩) (y := ⟨q ^ 2, hq2Z⟩) ?_ ?_)
      · exact orderOf_eq_prime (Subtype.ext hd2) (fun hh => hd1 (congrArg Subtype.val hh))
      · rw [← Subgroup.orderOf_coe]; exact hq2H
    exact hdeq ▸ Q.pow_mem hq 2
  exact Q.mul_mem hq hdQ

/-- A quaternion-eight supplement to a cyclic center is characteristic:
its noncentral elements are exactly the ambient noncentral elements of order four. -/
public theorem quaternion_supplement_characteristic
    {H : Type*} [Group H] [Finite H] [IsCyclic (center H)]
    (Q : Subgroup H) (e : Q ≃* QuaternionGroup 2)
    (hgen : Q ⊔ center H = ⊤) : Q.Characteristic := by
  let f : QuaternionGroup 2 →* H := Q.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := Q.subtype_injective.comp e.symm.injective
  let a : H := f (QuaternionGroup.a 1)
  let b : H := f (QuaternionGroup.xa 0)
  have hnc : a * b ≠ b * a := by
    intro hh
    have he : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 =
        QuaternionGroup.xa 0 * QuaternionGroup.a 1 := hf (by simpa only [map_mul] using hh)
    exact (by decide : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 ≠
      QuaternionGroup.xa 0 * QuaternionGroup.a 1) he
  have ha4 : orderOf a = 4 := (orderOf_injective f hf _).trans QuaternionGroup.orderOf_a_one
  have hb4 : orderOf b = 4 := (orderOf_injective f hf _).trans (QuaternionGroup.orderOf_xa _)
  apply characteristic_iff_le_comap.mpr
  intro φ x hx
  have himage (u v : H) (hu4 : orderOf u = 4) (huv : u * v ≠ v * u) : φ u ∈ Q := by
    apply quaternion_supplement_contains_noncentral_four Q e hgen
    · intro hu
      apply huv
      apply φ.injective
      simpa only [map_mul] using (mem_center_iff.mp hu (φ v)).symm
    · exact (φ.orderOf_eq u).trans hu4
  have ha : φ a ∈ Q := himage a b ha4 hnc
  have hb : φ b ∈ Q := himage b a hb4 (Ne.symm hnc)
  change φ x ∈ Q
  have hx' : f (e ⟨x, hx⟩) = x := by simp [f]
  rw [← hx']
  cases e ⟨x, hx⟩ with
  | a i =>
    have hi : (QuaternionGroup.a i : QuaternionGroup 2) = QuaternionGroup.a 1 ^ i.val := by simp
    rw [hi, map_pow, map_pow]
    exact Q.pow_mem ha _
  | xa i =>
    have hi : (QuaternionGroup.xa i : QuaternionGroup 2) =
        QuaternionGroup.xa 0 * QuaternionGroup.a 1 ^ i.val := by simp
    rw [hi, map_mul, map_pow, map_mul, map_pow]
    exact Q.mul_mem hb (Q.pow_mem ha _)

/-- An extraspecial factor of order eight with a commuting cyclic tail of
order at least eight has a characteristic quaternion-eight supplement to
that tail. The extraspecial factor itself may be dihedral. -/
public theorem exists_characteristic_quaternion_of_extraspecial_cyclic_product
    {H : Type*} [Group H] [Finite H] [IsCyclic (center H)]
    (hH : IsPGroup 2 H) (B D : Subgroup H) [B.Normal] [D.Normal]
    [IsExtraspecial 2 B] [IsCyclic D] (hB : Nat.card B = 8)
    (hD : 8 ≤ Nat.card D) (hc : D ≤ centralizer (B : Set H))
    (hgen : B ⊔ D = ⊤) :
    ∃ Q : Subgroup H, Q.Characteristic ∧ Nonempty (Q ≃* QuaternionGroup 2) ∧
      Q ⊔ D = ⊤ := by
  have hDne : D ≠ ⊥ := by intro h; simp [h] at hD
  have hcenter : center H = D :=
    center_eq_cyclic_factor_of_extraspecial_of_cyclic_center hH B D hDne hc hgen
  have hgenZ : B ⊔ center H = ⊤ := by rwa [hcenter]
  have hrank (U : Subgroup B) (hU : IsElementaryAbelian 2 U) : Nat.card U < 8 := by
    let : IsElementaryAbelian 2 U := hU
    exact IsExtraspecial.elementary_card_lt_eight_of_card_lt_thirty_two
      (by rw [hB]; decide) U
  have hmodels : Nonempty (B ≃* DihedralGroup 4) ∨ Nonempty (B ≃* QuaternionGroup 2) := by
    rcases IsExtraspecial.rank_two_classification hrank with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · obtain ⟨U, V, ⟨eU⟩, ⟨eV⟩, hcomm, hjoin, hi⟩ := h
      have hUcard : Nat.card U = 8 := by
        rw [Nat.card_congr eU.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
      have hVcard : Nat.card V = 8 := by
        rw [Nat.card_congr eV.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
      have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes U V
        (hcomm.trans (centralizer_le_normalizer _))
      rw [hUcard, hVcard, hi, hjoin, card_top, hB] at hh
      omega
  obtain ⟨Q, ⟨eQ⟩, hQgen⟩ : ∃ Q : Subgroup H,
      Nonempty (Q ≃* QuaternionGroup 2) ∧ Q ⊔ center H = ⊤ := by
    rcases hmodels with hBdihedral | hBquat
    · obtain ⟨eB⟩ := hBdihedral
      exact quaternion_supplement_of_dihedral hH B eB hgenZ
        (by rw [hcenter]; omega)
    · exact ⟨B, hBquat, hgenZ⟩
  exact ⟨Q, quaternion_supplement_characteristic Q eQ hQgen, ⟨eQ⟩,
    by rwa [← hcenter]⟩

end Subgroup
