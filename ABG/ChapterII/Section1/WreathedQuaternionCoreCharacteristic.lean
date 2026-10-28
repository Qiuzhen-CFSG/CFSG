module
public import ABG.ChapterII.Section1.WreathedCentralProductLocal

/-!
# The characteristic quaternion core of the wreathed central product

The quaternion core is characteristic in the canonical central product V.
This formalizes the assertion that the three noncentral cyclic subgroups
of order four in V are precisely those of the quaternion core, used in
Alperin--Brauer--Gorenstein, Chapter II Section 1 Proposition 2, article
p.13, `refs/latex/alperin-brauer-gorenstein-pages/page-014.tex`.
It permits normalizer actions on V to restrict to its actual quaternion
factor in the outer automizer and focal calculations.

The cyclic ambient center has a unique involution x. Every noncentral
quaternion element has order four and square x. Write an element v of V
as q*c with q in the quaternion core and c central. If v is noncentral
of order four, its central square is also x, forcing c^2=1 and hence c
into the core. Automorphisms of V preserve its center, which equals the
ambient center, as well as element orders. Thus the noncentral elements
of the core stay in it. Its central elements have square one, so their
images stay in the unique central involution subgroup, also in the core.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

private theorem central_square_one {c : S} (hc : c ∈ Subgroup.center S)
    (hsq : c ^ 2 = 1) : c ∈ Subgroup.zpowers P.x := by
  rw [P.center_eq_zpowers] at hc
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  have hd : ((2 ^ n : ℕ) : ℤ) ∣ k * 2 := by
    rw [← P.orderOf_u]
    apply orderOf_dvd_iff_zpow_eq_one.mpr
    simpa [zpow_mul] using hsq
  have hm : ((2 ^ n : ℕ) : ℤ) = ((2 ^ (n-1) : ℕ) : ℤ) * 2 := by
    norm_cast
    rw [← pow_succ]
    congr 1
    have := P.height
    omega
  rw [hm, mul_dvd_mul_iff_right (by decide : (2 : ℤ) ≠ 0)] at hd
  obtain ⟨a, ha⟩ := hd
  rw [ha, zpow_mul, zpow_natCast]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers P.x) _

private theorem central_involution_eq_x {c : S} (hc : c ∈ Subgroup.center S)
    (ho : orderOf c = 2) : c = P.x := by
  have hs := P.central_square_one hc (ho ▸ pow_orderOf_eq_one c)
  obtain ⟨k,rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
  have hs : P.x ^ (2 : ℕ) = 1 := P.x_orderOf ▸ pow_orderOf_eq_one P.x
  have hs' : P.x ^ (2 : ℤ) = 1 := by simpa using hs
  rw [zpow_eq_zpow_emod k hs']
  have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hk with hk | hk
  · rw [zpow_eq_zpow_emod k hs', hk, zpow_zero, orderOf_one] at ho
    omega
  · simp [hk]

private theorem core_order_four {q : S} (hq : q ∈ P.quaternionCore)
    (hn : q ∉ Subgroup.center S) : orderOf q = 4 := by
  obtain ⟨e⟩ := P.quaternion_core_model.1
  have hs : (e ⟨q, hq⟩) ^ 2 ≠ 1 := by
    intro hs
    have hc : e ⟨q, hq⟩ ∈ Subgroup.center (QuaternionGroup 2) := by
      have hsmall : ∀ a : QuaternionGroup 2, a ^ 2 = 1 →
          ∀ b : QuaternionGroup 2, b * a = a * b := by decide
      exact Subgroup.mem_center_iff.mpr (hsmall _ hs)
    apply hn
    apply P.nonabelian_center_le P.quaternionCore P.quaternion_core_noncommutative
    refine ⟨⟨q,hq⟩, ?_, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro b
    apply e.injective
    simpa only [map_mul] using Subgroup.mem_center_iff.mp hc (e b)
  have hsmall : ∀ a : QuaternionGroup 2, a ^ 4 = 1 := by decide
  have heq : orderOf (e ⟨q,hq⟩) = 2 ^ 2 := by
    apply orderOf_eq_prime_pow
    · simpa using hs
    · exact hsmall _
  rw [e.orderOf_eq] at heq
  simpa only [← Subgroup.orderOf_coe, Nat.reducePow] using heq

private theorem core_square {q : S} (hq : q ∈ P.quaternionCore)
    (hn : q ∉ Subgroup.center S) : q ^ 2 = P.x := by
  have ho := P.core_order_four hq hn
  have hcenter : q ^ 2 ∈ Subgroup.center S := by
    obtain ⟨e⟩ := P.quaternion_core_model.1
    apply P.nonabelian_center_le P.quaternionCore P.quaternion_core_noncommutative
    refine ⟨(⟨q,hq⟩ : P.quaternionCore) ^ 2, ?_, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro b
    apply e.injective
    simp only [map_mul, map_pow]
    have hsmall : ∀ a b : QuaternionGroup 2, b * a ^ 2 = a ^ 2 * b := by decide
    exact hsmall _ _
  apply P.central_involution_eq_x hcenter
  rw [orderOf_pow' _ (by decide : (2 : ℕ) ≠ 0), ho]
  decide

private theorem noncentral_order_four_mem_core {v : S} (hv : v ∈ P.V)
    (hn : v ∉ Subgroup.center S) (ho : orderOf v = 4) : v ∈ P.quaternionCore := by
  obtain ⟨q,hq,c,hc,rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hv
  have hqn : q ∉ Subgroup.center S := by
    intro h
    exact hn ((Subgroup.center S).mul_mem h hc)
  have hcomm : Commute q c := (Subgroup.mem_center_iff.mp hc q)
  have hsq : (q * c) ^ 2 = P.x := by
    apply P.central_involution_eq_x
    · rw [hcomm.mul_pow, P.core_square hq hqn]
      exact (Subgroup.center S).mul_mem P.x_mem_center ((Subgroup.center S).pow_mem hc 2)
    · rw [orderOf_pow' _ (by decide : (2 : ℕ) ≠ 0), ho]
      decide
  rw [hcomm.mul_pow, P.core_square hq hqn, mul_eq_left] at hsq
  have hcQ : c ∈ P.quaternionCore :=
    (Subgroup.zpowers_le.mpr P.x_mem_quaternionCore) (P.central_square_one hc hsq)
  exact P.quaternionCore.mul_mem hq hcQ

private theorem V_mem_center_iff (v : P.V) :
    v ∈ Subgroup.center P.V ↔ (v : S) ∈ Subgroup.center S := by
  rw [← P.V_center]
  exact (Subgroup.mem_map_iff_mem P.V.subtype_injective).symm

private theorem V_aut_mem_center_iff (f : MulAut P.V) (v : P.V) :
    (f v : S) ∈ Subgroup.center S ↔ (v : S) ∈ Subgroup.center S := by
  rw [← P.V_mem_center_iff, ← P.V_mem_center_iff]
  constructor
  · intro h
    apply Subgroup.mem_center_iff.mpr
    intro a
    apply f.injective
    simpa only [map_mul] using Subgroup.mem_center_iff.mp h (f a)
  · intro h
    apply Subgroup.mem_center_iff.mpr
    intro a
    obtain ⟨b,rfl⟩ := f.surjective a
    simpa only [map_mul] using congrArg f (Subgroup.mem_center_iff.mp h b)

/-- The actual quaternion subgroup is characteristic in its central product. -/
public theorem quaternionCore_characteristic_in_V :
    (P.quaternionCore.subgroupOf P.V).Characteristic := by
  rw [Subgroup.characteristic_iff_le_comap]
  intro f v hv
  change (f v : S) ∈ P.quaternionCore
  by_cases hc : (v : S) ∈ Subgroup.center S
  · have hx : (v : S) ∈ Subgroup.zpowers P.x := by
      rw [← P.quaternion_core_inf_center]
      exact ⟨hv,hc⟩
    have hs : (v : S) ^ 2 = 1 := by
      obtain ⟨k,hk⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm k, zpow_mul, zpow_natCast,
        ← P.x_orderOf, pow_orderOf_eq_one, one_zpow]
    have hvs : v ^ 2 = 1 := Subtype.ext hs
    have hfs : (f v : S) ^ 2 = 1 := by
      have h := congrArg f hvs
      rw [map_pow, map_one] at h
      exact congrArg Subtype.val h
    exact (Subgroup.zpowers_le.mpr P.x_mem_quaternionCore)
      (P.central_square_one ((P.V_aut_mem_center_iff f v).mpr hc) hfs)
  · apply P.noncentral_order_four_mem_core (f v).property
    · exact fun h => hc ((P.V_aut_mem_center_iff f v).mp h)
    · rw [Subgroup.orderOf_coe, f.orderOf_eq, ← Subgroup.orderOf_coe]
      exact P.core_order_four hv hc

end ABG.Wreathed.Presentation
