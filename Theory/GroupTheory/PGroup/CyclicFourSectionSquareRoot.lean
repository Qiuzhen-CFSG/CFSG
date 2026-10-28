module

public import Theory.GroupTheory.PGroup.CyclicFourSectionAssembly
public import Theory.GroupTheory.NormalSubgroupInvolutionFiber
public import Theory.GroupTheory.PGroup.NormalExtraspecialDerivedCenter

/-!
# Cyclic-four sections from square roots of the core action

Let `H` be a normal self-centralizing extraspecial subgroup of a finite
two-group `P`, with cyclic quotient of order four. An outside involution
acts on `H` by an inner twist of the square of a quotient generator's action.
If that action has an elementary fixed four and an inner correction gives
an automorphism square root, then `P` contains a cyclic-four section with
central kernel containing the specified involution.

The corrected lift squares to the involution modulo the ambient center.
Its cyclic subgroup together with that center supplements `H` and meets
`H` centrally. The fixed four is normal, hence equals the unique normal
four when this is specified. The finite automorphism calculation is retained
as an explicit input, independently of the ambient transfer proved here.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed p.390,
the cyclic-four normalizer section and fixed-core calculation.
-/

open Subgroup
namespace Subgroup
variable {P : Type*} [Group P] [Finite P]

/-- A square root modulo the ambient center yields a supplement with central intersection. -/
public theorem central_supplement_of_square_mod_center
    (H : Subgroup P) [H.Normal] (hindex : H.index = 4)
    (hZH : center P ≤ H) (s t : P) (ht : t ^ 2 = 1)
    (hs : orderOf (QuotientGroup.mk' H s) = 4)
    (hroot : s ^ 2 * t⁻¹ ∈ center P) :
    ∃ K : Subgroup P, K ⊔ H = ⊤ ∧ K ⊓ H ≤ center P ∧ t ∈ K := by
  let K := zpowers s ⊔ center P
  let q := QuotientGroup.mk' H
  have hfour : s ^ 4 ∈ center P := by
    have hc : Commute (s ^ 2 * t⁻¹) t :=
      (show Commute t (s ^ 2 * t⁻¹) from mem_center_iff.mp hroot t).symm
    have he : s ^ 4 = (s ^ 2 * t⁻¹) ^ 2 := by
      have hh := hc.mul_pow 2
      have hid : (s ^ 2 * t⁻¹) * t = s ^ 2 := by group
      rw [hid, ht, mul_one] at hh
      simpa only [← pow_mul] using hh
    rw [he]
    exact (center P).pow_mem hroot 2
  have hgen : zpowers (q s) = ⊤ := by
    apply (card_eq_iff_eq_top _).mp
    rw [Nat.card_zpowers, hs]
    exact hindex.symm
  have hsup : K ⊔ H = ⊤ := by
    have hm : K.map q = ⊤ := top_unique (by
      rw [← hgen, ← MonoidHom.map_zpowers]
      exact map_mono le_sup_left)
    have hh := congrArg (Subgroup.comap q) hm
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using hh
  refine ⟨K, hsup, ?_, ?_⟩
  · rintro x ⟨hxK, hxH⟩
    obtain ⟨y, hy, c, hc, rfl⟩ := mem_sup_of_normal_right.mp hxK
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
    have hpowH : s ^ n ∈ H := (H.mul_mem_cancel_right (hZH hc)).mp hxH
    have hn : (4 : ℤ) ∣ n := by
      have hh : (q s) ^ n = 1 := by
        rw [← map_zpow]
        exact (QuotientGroup.eq_one_iff _).mpr hpowH
      simpa only [q, hs, Nat.cast_ofNat] using orderOf_dvd_iff_zpow_eq_one.mpr hh
    obtain ⟨k, rfl⟩ := hn
    apply (center P).mul_mem _ hc
    rw [zpow_mul]
    exact (center P).zpow_mem (by simpa using hfour) k
  · have hsK : s ^ 2 ∈ K := mem_sup_left ((zpowers s).pow_mem (mem_zpowers s) 2)
    have hcK : s ^ 2 * t⁻¹ ∈ K := mem_sup_right hroot
    have hh := K.mul_mem (K.inv_mem hcK) hsK
    simpa only [mul_inv_rev, inv_inv, inv_mul_cancel_right] using hh

/-- A central square root and an elementary fixed four give a cyclic-four section. -/
public theorem cyclic_four_section_of_square_mod_center
    (H W : Subgroup P) [H.Normal] [IsCyclic (P ⧸ H)]
    (hindex : H.index = 4) (hZH : center P ≤ H)
    (hclass : ⁅H, H⁆ ≤ center P)
    (hunique : ∀ F : Subgroup P, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (s t : P) (ht : t ^ 2 = 1)
    (hs : orderOf (QuotientGroup.mk' H s) = 4)
    (hroot : s ^ 2 * t⁻¹ ∈ center P)
    (hfixed : IsElementaryAbelian 2 (H ⊓ centralizer ({t} : Set P) : Subgroup P))
    (hcard : Nat.card (H ⊓ centralizer ({t} : Set P) : Subgroup P) = 4) :
    ∃ (K : Subgroup P) (Z : Subgroup K) (_ : Z.Normal),
      IsCyclic (K ⧸ Z) ∧ Nat.card (K ⧸ Z) = 4 ∧
      Z ≤ (center P).comap K.subtype ∧ t ∈ K ∧
      H ⊓ centralizer ({t} : Set P) = W := by
  obtain ⟨K, hsup, hcentral, htK⟩ :=
    central_supplement_of_square_mod_center H hindex hZH s t ht hs hroot
  obtain ⟨Z, hZn, hcyclic, hquot, hZc, hFW, _⟩ :=
    cyclic_four_centralizer_section_of_supplement H W K hindex hunique
      hsup hcentral hclass t htK hfixed hcard
  exact ⟨K, Z, hZn, hcyclic, hquot, hZc, htK, hFW⟩

/-- Transfer a square-action calculation on a self-centralizing extraspecial core
to a cyclic-four section in the ambient two-group. -/
public theorem bare_section_of_extraspecial_square_action
    (hP : IsPGroup 2 P) (H W : Subgroup P) [H.Normal] [IsExtraspecial 2 H]
    (hself : centralizer (H : Set P) ≤ H)
    (hindex : H.index = 4) [IsCyclic (P ⧸ H)]
    (hunique : ∀ F : Subgroup P, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hcalc : ∀ (a b : MulAut H) (p : H) (n : ℕ),
      b ^ (2 ^ n) = 1 → a = MulAut.conj p * b ^ 2 → a ^ 2 = 1 →
      (¬ ∃ x : H, a = MulAut.conj x) →
      IsElementaryAbelian 2 (a.toMonoidHom.eqLocus (MonoidHom.id H)) ∧
      Nat.card (a.toMonoidHom.eqLocus (MonoidHom.id H)) = 4 ∧
      ∃ x : H, (MulAut.conj x * b) ^ 2 = a)
    (t : P) (ht : orderOf t = 2) (hout : t ∉ H) :
    ∃ (K : Subgroup P) (Z : Subgroup K) (_ : Z.Normal),
      IsCyclic (K ⧸ Z) ∧ Nat.card (K ⧸ Z) = 4 ∧
      Z ≤ (center P).comap K.subtype ∧ t ∈ K ∧
      H ⊓ centralizer ({t} : Set P) = W := by
  let e := MulEquiv.refl H
  let a := normalConjThrough H e
  let q := QuotientGroup.mk' H
  have ht2 : t ^ 2 = 1 := by simpa only [ht] using pow_orderOf_eq_one t
  have ha2 : a t ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  have haout : ¬ ∃ x : H, a t = MulAut.conj x :=
    normalConjThrough_not_inner H e hself t hout
  have hquot : Nat.card (P ⧸ H) = 4 := hindex
  have hqt : (q t) ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  have hqtne : q t ≠ 1 := fun h => hout ((QuotientGroup.eq_one_iff _).mp h)
  obtain ⟨b, hb⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := P ⧸ H)
  rw [hquot] at hb
  have hb2 : orderOf (b ^ 2) = 2 := by rw [orderOf_pow, hb]; norm_num
  have hroot : b ^ 2 = q t :=
    IsCyclic.eq_of_orderOf_eq_two hb2 (orderOf_eq_prime hqt hqtne)
  obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective H b
  have hsH : t * (s ^ 2)⁻¹ ∈ H := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (t * (s ^ 2)⁻¹) = 1
    rw [map_mul, map_inv, map_pow, hroot, mul_inv_cancel]
  let p : H := ⟨t * (s ^ 2)⁻¹, hsH⟩
  have htp : t = (p : P) * s ^ 2 := by simp [p]
  obtain ⟨n, hn⟩ := hP.exists_pow_pow_eq_one s
  have has : a s ^ (2 ^ n) = 1 := by rw [← map_pow, hn, map_one]
  have hat : a t = MulAut.conj p * a s ^ 2 := by
    rw [htp, map_mul, map_pow]
    congr 1
    exact normalConjThrough_coe H e p
  obtain ⟨helem, hcard, x, hx⟩ := hcalc (a t) (a s) p n has hat ha2 haout
  obtain ⟨helem', hcard'⟩ := normalConjThrough_fixed_elementary_card H e t 4 helem hcard
  have hZcentral : (center H).map H.subtype ≤ center P :=
    central_of_normal_card_two _ (by
      rw [card_map_of_injective H.subtype_injective, IsExtraspecial.center_order_p 2 H])
  have hclass : ⁅H, H⁆ ≤ center P := by
    rw [← map_subtype_commutator, IsExtraspecial.commutator_eq_center_two]
    exact hZcentral
  have hZH : center P ≤ H := (center_le_centralizer _).trans hself
  have hker : a.ker ≤ center P := by
    intro u hu
    have hC : u ∈ centralizer (H : Set P) := by
      intro y hy
      have hh := congrArg (fun f : MulAut H => (f ⟨y, hy⟩ : P)) hu
      change u * y * u⁻¹ = y at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    apply hZcentral
    refine ⟨⟨u, hself hC⟩, mem_center_iff.mpr ?_, rfl⟩
    intro y
    exact Subtype.ext (hC y y.property)
  let r : P := (x : P) * s
  have har : a r = MulAut.conj x * a s := by
    rw [map_mul]
    congr 1
    exact normalConjThrough_coe H e x
  have hrroot : r ^ 2 * t⁻¹ ∈ center P := by
    apply hker
    change a (r ^ 2 * t⁻¹) = 1
    rw [map_mul, map_pow, map_inv, har, hx, mul_inv_cancel]
  have hqr : q r = q s := by
    have hxq : q x = 1 := (QuotientGroup.eq_one_iff _).mpr x.property
    change q ((x : P) * s) = q s
    rw [map_mul, hxq, one_mul]
  apply cyclic_four_section_of_square_mod_center H W hindex hZH hclass hunique
    r t ht2 _ hrroot helem' hcard'
  change orderOf (q r) = 4
  rw [hqr]
  exact hb
end Subgroup
