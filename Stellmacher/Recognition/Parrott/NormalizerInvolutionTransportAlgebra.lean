module

public import Stellmacher.Recognition.Parrott.NormalizerTransportData

/-!
# Commutator deductions for the normalizer transport

An involution in N_G(F) sending y to wuvz automatically sends t to z and
v to vtz. The first deduction uses [y,u] = t and the fact that wuvz acts
on F by a transvection with image contained in ⟨z⟩. The second uses
[y,wuvz] = vt and the fact that the selected involution interchanges its
two arguments. All coordinates in the supplied frame are retained.

The action and commutator calculations are also available to the preceding
involution-orbit construction. No normalizer involution is asserted to exist
in this module.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.681, “Generators and relations for N”.
-/

open Subgroup
open scoped IsMulCommutative

namespace Stellmacher.Recognition

variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

private theorem tail {a b c : G} (h : a * b = c) (k : G) :
    a * (b * k) = c * k := by rw [← mul_assoc, h]
private theorem inv_of_sq {g : G} (h : g ^ 2 = 1) : g⁻¹ = g :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using h)
private theorem conj_of_comm {p q c : G} (h : Tits.parrottCommutator p q = c)
    (hc : c ^ 2 = 1) : (MulAut.conj p⁻¹) q = q * c := by
  have hh := (Tits.parrottCommutator_eq_iff _ _ _).mp h
  change p⁻¹ * q * p⁻¹⁻¹ = q * c
  rw [inv_inv]
  calc
    p⁻¹ * q * p = p⁻¹ * (p * q) * c⁻¹ := by rw [hh]; group
    _ = q * c := by rw [inv_of_sq hc]; group
private theorem square_conj (f : ParrottSylowGeneratorData n) (g : G)
    (hg : Commute z g) :
    (MulAut.conj f.y⁻¹) g = (MulAut.conj f.x⁻¹) ((MulAut.conj f.x⁻¹) g) := by
  have hy : f.y = f.x ^ 2 * z⁻¹ := by rw [f.eq04]; group
  rw [hy]
  change _ * g * _ = _ * (_ * g * _) * _
  simp only [mul_inv_rev, inv_inv, pow_two]
  simp only [mul_assoc, tail f.comm_zx.inv_right.eq, tail hg.eq,
    tail f.comm_zx.eq, mul_inv_cancel, mul_one]

/-- The action of y on the last three derived-basis coordinates, obtained
by squaring the action of x and using x² = yz. -/
public theorem ParrottSylowGeneratorData.y_conjugation (f : ParrottSylowGeneratorData n) :
    (MulAut.conj f.y⁻¹) n.v = n.v ∧
    (MulAut.conj f.y⁻¹) f.u = f.u * n.t ∧
    (MulAut.conj f.y⁻¹) f.w = f.w * n.v := by
  have ht : (MulAut.conj f.x⁻¹) n.t = n.t := by
    simpa using conj_of_comm f.eq01_xt (by simp)
  have hv := conj_of_comm f.eq01_xv f.t_sq
  have hu := conj_of_comm f.eq01_xu f.v_sq
  have hw := conj_of_comm f.eq01_xw f.u_sq
  refine ⟨?_, ?_, ?_⟩
  · rw [square_conj f n.v f.comm_zv, hv, map_mul, hv, ht]
    simp only [mul_assoc, ← pow_two, f.t_sq, mul_one]
  · rw [square_conj f f.u f.comm_zu, hu, map_mul, hu, hv]
    simp only [mul_assoc, tail (show n.v * n.v = 1 from by simpa only [pow_two] using f.v_sq), one_mul]
  · rw [square_conj f f.w f.comm_zw, hw, map_mul, hw, hu]
    simp only [mul_assoc, tail (show f.u * f.u = 1 from by simpa only [pow_two] using f.u_sq), one_mul]
private theorem conj_of_commute {p q : G} (h : Commute p q) :
    (MulAut.conj p⁻¹) q = q := by
  change p⁻¹ * q * p⁻¹⁻¹ = q
  rw [h.inv_left.eq, inv_inv, mul_assoc, inv_mul_cancel, mul_one]

/-- Conjugation by wuvz changes an element of F by at most z. -/
public theorem ParrottSylowGeneratorData.wuvz_action_on_elementary (f : ParrottSylowGeneratorData n) (g : G) (hg : g ∈ e.F) :
    (MulAut.conj (f.w * f.u * n.v * z)⁻¹) g = g ∨
    (MulAut.conj (f.w * f.u * n.v * z)⁻¹) g = g * z := by
  let _ := e.elementary
  have hc (g : G) (hg : g ∈ e.F) : Commute z g := by
    exact congrArg e.F.subtype (mul_comm (⟨z, e.z_mem_inf.2⟩ : e.F) ⟨g, hg⟩)
  have hwa : f.w * f.a = f.a * f.w * z := by
    rw [(Tits.parrottCommutator_eq_iff _ _ _).mp f.eq02_aw]
    simp only [mul_assoc, ← pow_two, f.z_sq, mul_one]
  have hRa : Tits.parrottCommutator (f.w * f.u * n.v * z) f.a = z := by
    apply (Tits.parrottCommutator_eq_iff _ _ _).mpr
    simp only [mul_assoc, f.comm_az.symm.eq, tail f.comm_av.symm.eq,
      tail f.comm_au.symm.eq, tail hwa, tail f.comm_zu.eq, tail f.comm_zv.eq]
  rw [← f.elementary_basis] at hg
  induction hg using closure_induction with
  | mem g hg =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (conj_of_commute (((f.comm_zw.symm.mul_left f.comm_zu.symm).mul_left
        f.comm_zv.symm).mul_left (Commute.refl _)))
    · exact Or.inl (conj_of_commute (((f.comm_tw.symm.mul_left f.comm_tu.symm).mul_left
        f.comm_tv.symm).mul_left f.comm_zt))
    · exact Or.inl (conj_of_commute (((f.comm_vw.symm.mul_left f.comm_vu.symm).mul_left
        (Commute.refl n.v)).mul_left f.comm_zv))
    · exact Or.inl (conj_of_commute (((f.comm_uw.symm.mul_left (Commute.refl f.u)).mul_left
        f.comm_vu).mul_left f.comm_zu))
    · exact Or.inr (conj_of_comm hRa f.z_sq)
  | one => exact Or.inl (map_one _)
  | mul g k hg hk ihg ihk =>
    have hzk := hc k (f.elementary_basis ▸ hk)
    rw [map_mul]
    rcases ihg with hg' | hg' <;> rcases ihk with hk' | hk'
    · exact Or.inl (by rw [hg', hk'])
    · exact Or.inr (by rw [hg', hk', mul_assoc])
    · exact Or.inr (by rw [hg', hk']; simp only [mul_assoc, hzk.eq])
    · exact Or.inl (by rw [hg', hk']; simp only [mul_assoc, tail hzk.eq, ← pow_two, f.z_sq, mul_one])
  | inv g hg ih =>
    have hi : g⁻¹ = g := inv_of_sq (elemPow_eq_one_of_isElementaryAbelian g
      (show g ∈ e.F from f.elementary_basis ▸ hg))
    simpa only [hi] using ih
private theorem comm_via_conj (p q : G) :
    Tits.parrottCommutator p q = ((MulAut.conj p⁻¹) q)⁻¹ * q := by
  simp only [Tits.parrottCommutator, MulAut.conj_apply, mul_inv_rev, inv_inv]
  group
private theorem comm_map (φ : MulAut G) (p q : G) :
    φ (Tits.parrottCommutator p q) = Tits.parrottCommutator (φ p) (φ q) := by
  simp only [Tits.parrottCommutator, map_mul, map_inv]
/-- The commutator used to recover the image of v once y has been transported. -/
public theorem ParrottSylowGeneratorData.y_wuvz_commutator (f : ParrottSylowGeneratorData n) :
    Tits.parrottCommutator f.y (f.w * f.u * n.v * z) = n.v * n.t := by
  have ha := ParrottSylowGeneratorData.y_conjugation f
  have hz := conj_of_commute f.comm_zy.symm
  have hconj : (MulAut.conj f.y⁻¹) (f.w * f.u * n.v * z) =
      (f.w * f.u * n.v * z) * (n.v * n.t) := by
    rw [map_mul, map_mul, map_mul, ha.1, ha.2.1, ha.2.2, hz]
    simp only [mul_assoc, tail f.comm_vu.eq, tail f.comm_tv.eq,
      tail f.comm_zv.eq, f.comm_zt.eq,
      tail (show n.v * n.v = 1 from by simpa only [pow_two] using f.v_sq), one_mul]
  rw [comm_via_conj, hconj]
  rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one, mul_inv_rev,
    inv_of_sq f.t_sq, inv_of_sq f.v_sq, f.comm_tv.eq]

private theorem t_image (f : ParrottSylowGeneratorData n) (s : G)
    (hsN : s ∈ normalizer (e.F : Set G))
    (hy : s⁻¹ * f.y * s = f.w * f.u * n.v * z) : s⁻¹ * n.t * s = z := by
  let φ := MulAut.conj s⁻¹
  have hy' : φ f.y = f.w * f.u * n.v * z := by simpa [φ] using hy
  have huF : f.u ∈ e.F := by
    rw [← f.elementary_basis]
    exact subset_closure (by simp)
  have hφuF : φ f.u ∈ e.F := by
    simpa [φ] using (mem_normalizer_iff''.mp hsN f.u).mp huF
  have hyt : Tits.parrottCommutator f.y f.u = n.t := by
    rw [comm_via_conj, (ParrottSylowGeneratorData.y_conjugation f).2.1]
    simp only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one, inv_of_sq f.t_sq]
  have hφt : φ n.t = Tits.parrottCommutator (f.w * f.u * n.v * z) (φ f.u) := by
    rw [← hyt, comm_map, hy']
  have hcases := ParrottSylowGeneratorData.wuvz_action_on_elementary f (φ f.u) hφuF
  rw [comm_via_conj] at hφt
  have htz : φ n.t = 1 ∨ φ n.t = z := by
    rcases hcases with hc | hc
    · exact Or.inl (by rw [hφt, hc, inv_mul_cancel])
    · exact Or.inr (by rw [hφt, hc]; simp only [mul_inv_rev, mul_assoc,
        inv_mul_cancel, mul_one, inv_of_sq f.z_sq])
  rcases htz with ht | ht
  · have ht1 : n.t = 1 := φ.injective (ht.trans (map_one φ).symm)
    have hh := n.t_order
    rw [ht1, orderOf_one] at hh
    norm_num at hh
  · simpa [φ] using ht

private theorem v_image (f : ParrottSylowGeneratorData n) (s : G)
    (hs : s ^ 2 = 1)
    (ht : s⁻¹ * n.t * s = z)
    (hy : s⁻¹ * f.y * s = f.w * f.u * n.v * z) :
    s⁻¹ * n.v * s = n.v * n.t * z := by
  let φ := MulAut.conj s⁻¹
  have hy' : φ f.y = f.w * f.u * n.v * z := by simpa [φ] using hy
  have ht' : φ n.t = z := by simpa [φ] using ht
  have hR : φ (f.w * f.u * n.v * z) = f.y := by
    rw [← hy']
    change s⁻¹ * (s⁻¹ * f.y * s⁻¹⁻¹) * s⁻¹⁻¹ = f.y
    rw [inv_inv, inv_of_sq hs]
    have hss : s * s = 1 := by simpa only [pow_two] using hs
    simp only [← mul_assoc, hss, one_mul]
    rw [mul_assoc, hss, mul_one]
  have hswap : Tits.parrottCommutator (f.w * f.u * n.v * z) f.y = n.v * n.t := by
    calc
      _ = (Tits.parrottCommutator f.y (f.w * f.u * n.v * z))⁻¹ := by
        simp only [Tits.parrottCommutator, mul_inv_rev, inv_inv, mul_assoc]
      _ = n.v * n.t := by
        rw [ParrottSylowGeneratorData.y_wuvz_commutator f, mul_inv_rev, inv_of_sq f.t_sq, inv_of_sq f.v_sq, f.comm_tv.eq]
  have hh := congrArg φ (ParrottSylowGeneratorData.y_wuvz_commutator f)
  rw [comm_map, hy', hR, hswap, map_mul, ht'] at hh
  have : φ n.v = n.v * n.t * z := by
    calc
      φ n.v = (φ n.v * z) * z := by rw [mul_assoc, ← pow_two, f.z_sq, mul_one]
      _ = _ := by rw [← hh]
  simpa [φ] using this

/-- Complete all three transport equations from the selected image of y.
This construction does not change the supplied centralizer frame. -/
public def ParrottCentralizerGeneratorData.normalizerTransportOfYConj
    (f : ParrottCentralizerGeneratorData n) (s : G)
    (hsN : s ∈ normalizer (e.F : Set G)) (hs : s ^ 2 = 1)
    (hy : s⁻¹ * f.y * s = f.w * f.u * n.v * z) :
    ParrottNormalizerTransportData f where
  s := s
  mem_normalizer := hsN
  sq := hs
  t_conj := t_image f.toParrottSylowGeneratorData s hsN hy
  v_conj := v_image f.toParrottSylowGeneratorData s hs
    (t_image f.toParrottSylowGeneratorData s hsN hy) hy
  y_conj := hy

end Stellmacher.Recognition
