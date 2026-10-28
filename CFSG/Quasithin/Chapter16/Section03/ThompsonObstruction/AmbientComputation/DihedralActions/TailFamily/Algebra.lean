module

public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.AmbientComputation.DihedralActions.Products
public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.AmbientComputation.DihedralActions.ActionData
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# Rotation coordinates in the cyclic tail

Characteristicity of the rotation subgroup is used inside the centralizer
Sylow subgroup, then transported through the actual Sylow normalizer. This
supplies the compatible rotation/reflection/candidate normal forms.
In the faithful alternative, squaring in the rotation extension forces an
even rotation coordinate. Its involutions therefore lie in ⟨z,w⟩. Separately,
the conjugation relation shows that the centralizer of w in the tail lies in
⟨y²,t,w⟩. These statements concern individual elements and do not identify
an unrestricted omega subgroup with the maximum elementary family.

Source: Aschbacher--Smith, 16.3.12, printed pp.1181--1182 / PDF pp.1198--1199,
combined manuscript of 1 March 2004.
-/

public section

namespace CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation
open Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {z t : G} {L : Subgroup G}
namespace TailFamily

theorem involution_powers {w x : G} (hw : orderOf w = 2) (hx : x ∈ zpowers w) :
    x = 1 ∨ x = w := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hw] at hx
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hx
  have hi' : i < 2 := Finset.mem_range.mp hi
  interval_cases i
  · exact Or.inl (by simpa using he.symm)
  · exact Or.inr (by simpa using he.symm)

theorem involution_join_form (H : Subgroup G) {w x : G} (hw : orderOf w = 2)
    (hn : w ∈ normalizer (H : Set G)) (hx : x ∈ H ⊔ zpowers w) :
    ∃ v ∈ H, x = v ∨ x = v * w := by
  have hx' : x ∈ (H : Set G) * (zpowers w : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ (zpowers_le.mpr hn)]
    exact hx
  obtain ⟨v, hv, b, hb, rfl⟩ := hx'
  rcases involution_powers hw hb with rfl | rfl
  · exact ⟨v, hv, Or.inl (mul_one _)⟩
  · exact ⟨v, hv, Or.inr rfl⟩

omit [Finite G] in
theorem candidate_disjoint (d : Prepared T z t L) (a : ActionData d) :
    Disjoint (commutingSylow T L) (zpowers a.w) :=
  (commutingSylow_disjoint_component_candidate d a.candidate).mono_right le_sup_right

omit [Finite G] in
theorem candidate_outside (d : Prepared T z t L) (a : ActionData d) :
    a.w ∉ commutingSylow T L := by
  intro hw
  have h := disjoint_def.mp (candidate_disjoint d a) hw (mem_zpowers a.w)
  have ho := a.involution
  rw [h, orderOf_one] at ho
  omega

omit [Finite G] in
theorem rotation_normalized (d : Prepared T z t L) (a : ActionData d) :
    (T : Subgroup G) ≤ normalizer (zpowers a.y : Set G) := by
  let := a.rotation_characteristic
  have h := (sylow_normalizes_commutingSylow d).trans
    (normalizer_le_normalizer_characteristic_image (commutingSylow T L)
      ((zpowers a.y).subgroupOf (commutingSylow T L)))
  rwa [map_subgroupOf_eq_of_le a.rotation_le] at h

theorem rotation_form (d : Prepared T z t L) (a : ActionData d) {x : G}
    (hx : x ∈ commutingSylow T L) : ∃ k : ℕ, x = a.y ^ k ∨ x = a.y ^ k * t := by
  classical
  obtain ⟨v, hv, he⟩ := involution_join_form (zpowers a.y) d.counterexample.involution
    (rotation_normalized d a d.counterexample.mem_commutingSylow.1)
    (a.reflection_generation.symm ▸ hx)
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hv)
  exact ⟨k, he⟩

theorem tail_form (d : Prepared T z t L) (a : ActionData d) {x : G}
    (hx : x ∈ commutingSylow T L ⊔ zpowers a.w) :
    ∃ v ∈ commutingSylow T L, x = v ∨ x = v * a.w :=
  involution_join_form _ a.involution
    (sylow_normalizes_commutingSylow d (candidate_mem_and_centralizes d a.candidate).1) hx

omit [Finite G] in
theorem faithful_z_rotation (d : Prepared T z t L) (a : ActionData d)
    (hy : a.w⁻¹ * a.y * a.w = a.y * z) : z ∈ zpowers a.y := by
  have hn := rotation_normalized d a (candidate_mem_and_centralizes d a.candidate).1
  have hm := (mem_normalizer_iff''.mp hn a.y).mp (mem_zpowers a.y)
  rw [hy] at hm
  simpa only [inv_mul_cancel_left] using (zpowers a.y).mul_mem
    ((zpowers a.y).inv_mem (mem_zpowers a.y)) hm

omit [Finite G] in
theorem faithful_power_action (d : Prepared T z t L) (a : ActionData d)
    (hy : a.w⁻¹ * a.y * a.w = a.y * z) (k : ℕ) :
    a.w⁻¹ * a.y ^ k * a.w = a.y ^ k * z ^ k := by
  have hc : Commute a.y z := (zpowers a.y).le_centralizer
    (faithful_z_rotation d a hy) a.y (mem_zpowers a.y)
  calc
    _ = (a.w⁻¹ * a.y * a.w) ^ k := by
      have h := map_pow (MulAut.conj a.w⁻¹) a.y k
      simpa only [MulAut.conj_apply, inv_inv] using h
    _ = a.y ^ k * z ^ k := by rw [hy, hc.mul_pow]

theorem rotation_square_one (d : Prepared T z t L) (a : ActionData d)
    (hy : a.w⁻¹ * a.y * a.w = a.y * z) {v : G}
    (hv : v ∈ zpowers a.y) (hv2 : v ^ 2 = 1) : v ∈ zpowers z := by
  by_cases hv1 : v = 1
  · exact hv1 ▸ (zpowers z).one_mem
  have hvord : orderOf v = 2 := orderOf_eq_prime hv2 hv1
  have he : (⟨v, hv⟩ : zpowers a.y) = ⟨z, faithful_z_rotation d a hy⟩ :=
    IsCyclic.eq_of_orderOf_eq_two
      (by simpa only [← orderOf_coe] using hvord)
      (by simpa only [← orderOf_coe] using d.counterexample.localSetup.involution)
  have heq : v = z := congrArg Subtype.val he
  rw [heq]
  exact mem_zpowers z

/-- In the faithful modular rotation extension, every involution belongs to
    the central four-group generated by z and w. -/
theorem faithful_rotation_extension_involutions (d : Prepared T z t L) (a : ActionData d)
    (hlarge : 4 < orderOf a.y) (hy : a.w⁻¹ * a.y * a.w = a.y * z)
    {x : G} (hx : x ∈ zpowers a.y ⊔ zpowers a.w) (hx2 : x ^ 2 = 1) :
    x ∈ zpowers z ⊔ zpowers a.w := by
  classical
  have hw2 : a.w ^ 2 = 1 := by simpa only [a.involution] using pow_orderOf_eq_one a.w
  have hwi : a.w⁻¹ = a.w := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hw2)
  have hz2 : z ^ 2 = 1 := by
    simpa only [d.counterexample.localSetup.involution] using pow_orderOf_eq_one z
  obtain ⟨v, hv, hxe | hxe⟩ := involution_join_form (zpowers a.y) a.involution
    (rotation_normalized d a (candidate_mem_and_centralizes d a.candidate).1) hx
  · subst x
    exact mem_sup_left (rotation_square_one d a hy hv hx2)
  subst x
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hv)
  have hs : (a.y ^ k * a.w) ^ 2 = a.y ^ (2 * k) * z ^ k := by
    calc
      _ = a.y ^ k * (a.w⁻¹ * a.y ^ k * a.w) := by rw [hwi, pow_two]; group
      _ = a.y ^ k * (a.y ^ k * z ^ k) := by rw [faithful_power_action d a hy k]
      _ = a.y ^ (2 * k) * z ^ k := by rw [← mul_assoc, ← pow_add]; congr 2; omega
  have hc : Commute (a.y ^ (2 * k)) (z ^ k) :=
    (show Commute a.y z from (zpowers a.y).le_centralizer
      (faithful_z_rotation d a hy) a.y (mem_zpowers a.y)).pow_pow _ _
  have hy4 : a.y ^ (4 * k) = 1 := by
    have hh := congrArg (fun v : G => v ^ 2) (hs.symm.trans hx2)
    rw [hc.mul_pow, ← pow_mul z, Nat.mul_comm k 2, pow_mul z, hz2,
      one_pow, mul_one, ← pow_mul, one_pow] at hh
    convert hh using 1
    congr 1
    omega
  have hk : 2 ∣ k := by
    obtain ⟨n, hn, hord⟩ := a.rotation_order
    have hn3 : 3 ≤ n := by
      by_contra hn3
      have hn2 : n = 2 := by omega
      simp only [hn2, pow_two, Nat.reduceMul] at hord
      omega
    have hd8 : 8 ∣ orderOf a.y := by
      rw [hord]
      exact Nat.pow_dvd_pow 2 hn3
    have hd := hd8.trans (orderOf_dvd_of_pow_eq_one hy4)
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 4)).mp hd
  have hzk : z ^ k = 1 := by
    obtain ⟨j, rfl⟩ := hk
    rw [pow_mul, hz2, one_pow]
  have hy2 : (a.y ^ k) ^ 2 = 1 := by
    rw [hs, hzk, mul_one] at hx2
    simpa only [← pow_mul, Nat.mul_comm k 2] using hx2
  exact mul_mem_sup (rotation_square_one d a hy (pow_mem (mem_zpowers _) k) hy2)
    (mem_zpowers _)

/-- An element of the tail centralizing w has even rotation coordinate. -/
theorem faithful_centralizer_le (d : Prepared T z t L) (a : ActionData d)
    (hy : a.w⁻¹ * a.y * a.w = a.y * z)
    (hR : a.R = zpowers (a.y ^ 2) ⊔ zpowers t) :
    (commutingSylow T L ⊔ zpowers a.w) ⊓ centralizer ({a.w} : Set G) ≤
      a.R ⊔ zpowers a.w := by
  intro x hx
  have hc : Commute x a.w := mem_centralizer_singleton_iff.mp hx.2
  obtain ⟨v, hv, hxe | hxe⟩ := tail_form d a hx.1 <;>
    obtain ⟨k, hve | hve⟩ := rotation_form d a hv
  all_goals
    have hkw : Commute (a.y ^ k) a.w := by
      have htw := candidate_commutes_reflection d a.candidate
      rw [hxe, hve] at hc
      first
      | exact hc
      | exact (mul_right_cancel (show a.y ^ k * a.w * a.w = a.w * a.y ^ k * a.w by
          simpa only [mul_assoc] using hc.eq))
      | have hh := hc.mul_left htw.inv_right.symm
        simpa only [mul_inv_cancel_right] using hh
      | have hh := hc.mul_left (Commute.refl a.w).inv_left
        have hh' : Commute (a.y ^ k * t) a.w := by
          simpa only [mul_inv_cancel_right] using hh
        have hh'' := hh'.mul_left htw.inv_right.symm
        simpa only [mul_inv_cancel_right] using hh''
    have hzk : z ^ k = 1 := by
      have hfix : a.w⁻¹ * a.y ^ k * a.w = a.y ^ k := by
        rw [mul_assoc, hkw.eq, inv_mul_cancel_left]
      rw [faithful_power_action d a hy k] at hfix
      exact mul_left_cancel (hfix.trans (mul_one _).symm)
    have hk : 2 ∣ k := d.counterexample.localSetup.involution ▸
      orderOf_dvd_of_pow_eq_one hzk
    obtain ⟨j, rfl⟩ := hk
    have hm : a.y ^ (2 * j) ∈ a.R := by
      rw [hR, pow_mul]
      exact mem_sup_left (pow_mem (mem_zpowers _) _)
    have htR : t ∈ a.R := by rw [hR]; exact mem_sup_right (mem_zpowers _)
    rw [hxe, hve]
    first
    | exact mem_sup_left hm
    | exact mem_sup_left (a.R.mul_mem hm htR)
    | exact mul_mem_sup hm (mem_zpowers _)
    | exact mul_mem_sup (a.R.mul_mem hm htR) (mem_zpowers _)
end TailFamily
end CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation
