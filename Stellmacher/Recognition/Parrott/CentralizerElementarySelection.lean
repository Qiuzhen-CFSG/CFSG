module

public import Stellmacher.Recognition.Parrott.CentralizerInvolutionSeed
public import Stellmacher.Recognition.Parrott.CentralizerCoreOrientation
public import Stellmacher.Recognition.Parrott.CentralizerElementaryDuality

/-!
# Correcting the elementary action of Parrott's centralizer involution

For a supplied normalized Sylow frame, suppose an outer involution r satisfies
(ry)^5=1 and has the prescribed images of t,v modulo the original center ⟨z⟩.
Conjugation by b flips both central factors, and conjugation by a flips just
the factor in the t-image. Both a and b commute with y and belong to T.
These conjugations therefore preserve the fifth-power relation, involutivity,
and membership in H−T, while leaving every field of the Sylow frame unchanged.
They give the exact equations (20) and (21), with f'=f.

The geometric existence of an involution with these two images modulo ⟨z⟩
is a separate prerequisite. The results here discharge the compatibility of
central-factor correction and the fifth-power relation; they do not assume
that an arbitrary seed involution already has the required quotient action.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed pp.680–681, the replacements preceding equations (20) and (21).
The proof uses conjugations fixing y to perform the two central corrections.
-/

open Subgroup
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

private theorem rc_mul (k g g' : G) :
    k⁻¹ * (g * g') * k = (k⁻¹ * g * k) * (k⁻¹ * g' * k) := by group

private theorem rc_fixed {k g : G} (h : Commute k g) : k⁻¹ * g * k = g := by
  rw [mul_assoc, ← h.eq]
  simp

private theorem rc_commutator {a b c : G}
    (h : Tits.parrottCommutator a b = c) (hc : c ^ 2 = 1) :
    a⁻¹ * b * a = b * c := by
  have hswap := (Tits.parrottCommutator_eq_iff _ _ _).mp h
  have hcc : c * c = 1 := by simpa only [pow_two] using hc
  have heq := congrArg (fun g : G => a⁻¹ * g * c) hswap
  simpa only [mul_assoc, inv_mul_cancel_left, hcc, mul_one] using heq.symm

private theorem rc_conjugate {k g : G} (h : Commute k g) (r : G) :
    (k⁻¹ * r * k)⁻¹ * g * (k⁻¹ * r * k) = k⁻¹ * (r⁻¹ * g * r) * k := by
  have hh : k * g * k⁻¹ = g := by rw [h.eq]; group
  calc
    _ = k⁻¹ * r⁻¹ * (k * g * k⁻¹) * r * k := by group
    _ = _ := by rw [hh]; group

namespace ParrottSylowGeneratorData
variable (f : ParrottSylowGeneratorData n)

private theorem seed_conjugate (r k : G)
    (hrH : r ∈ centralizer ({z} : Set G)) (hrT : r ∉ e.sylow)
    (hr : r ^ 2 = 1) (hry : (r * f.y) ^ 5 = 1)
    (hk : k ∈ e.sylow) (hky : Commute k f.y) :
    k⁻¹ * r * k ∈ centralizer ({z} : Set G) ∧ k⁻¹ * r * k ∉ e.sylow ∧
      (k⁻¹ * r * k) ^ 2 = 1 ∧ ((k⁻¹ * r * k) * f.y) ^ 5 = 1 := by
  have hkH := e.sylow_le_centralizer hk
  refine ⟨mul_mem (mul_mem (inv_mem hkH) hrH) hkH, ?_, ?_, ?_⟩
  · intro hh
    have hm := (e.sylow : Subgroup G).mul_mem
      ((e.sylow : Subgroup G).mul_mem hk hh) ((e.sylow : Subgroup G).inv_mem hk)
    have heq : k * (k⁻¹ * r * k) * k⁻¹ = r := by group
    exact hrT (heq ▸ hm)
  · calc
      _ = k⁻¹ * r ^ 2 * k := by
        simpa only [inv_inv] using (conj_pow (a := k⁻¹) (b := r) (i := 2))
      _ = 1 := by rw [hr]; simp
  · have heq : (k⁻¹ * r * k) * f.y = k⁻¹ * (r * f.y) * k := by
      calc
        _ = k⁻¹ * r * (k * f.y) := by group
        _ = _ := by rw [hky.eq]; group
    rw [heq]
    calc
      _ = k⁻¹ * (r * f.y) ^ 5 * k := by
        simpa only [inv_inv] using (conj_pow (a := k⁻¹) (b := r * f.y) (i := 5))
      _ = 1 := by rw [hry]; simp

private theorem a_images :
    f.a⁻¹ * (f.w * f.u * n.v) * f.a = f.w * f.u * n.v * z ∧
      f.a⁻¹ * (f.u * n.v) * f.a = f.u * n.v := by
  have hw := rc_commutator f.eq02_aw f.z_sq
  have hu := rc_fixed f.comm_au
  have hv := rc_fixed f.comm_av
  constructor
  · rw [rc_mul, rc_mul, hw, hu, hv]
    calc
      _ = f.w * (z * f.u) * n.v := by group
      _ = f.w * (f.u * z) * n.v := by rw [f.comm_zu.eq]
      _ = f.w * f.u * (z * n.v) := by group
      _ = _ := by rw [f.comm_zv.eq]; group
  · rw [rc_mul, hu, hv]

private theorem b_images :
    f.b⁻¹ * (f.w * f.u * n.v) * f.b = f.w * f.u * n.v * z ∧
      f.b⁻¹ * (f.u * n.v) * f.b = f.u * n.v * z := by
  have hw := rc_fixed ((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq02_bw)
  have hu := rc_commutator f.eq02_bu f.z_sq
  have hv := rc_fixed (show Commute f.b n.v by
    rw [← f.eq03_b]; exact Commute.self_pow _ _)
  constructor
  · rw [rc_mul, rc_mul, hw, hu, hv]
    calc
      _ = f.w * f.u * (z * n.v) := by group
      _ = _ := by rw [f.comm_zv.eq]; group
  · rw [rc_mul, hu, hv, mul_assoc, f.comm_zv.eq, ← mul_assoc]

private theorem normalize_v (r : G)
    (hrH : r ∈ centralizer ({z} : Set G)) (hrT : r ∉ e.sylow)
    (hr : r ^ 2 = 1) (hry : (r * f.y) ^ 5 = 1)
    (ht : r⁻¹ * n.t * r = f.w * f.u * n.v ∨
      r⁻¹ * n.t * r = f.w * f.u * n.v * z)
    (hv : r⁻¹ * n.v * r = f.u * n.v ∨
      r⁻¹ * n.v * r = f.u * n.v * z) :
    ∃ r' : G, r' ∈ centralizer ({z} : Set G) ∧ r' ∉ e.sylow ∧
      r' ^ 2 = 1 ∧ (r' * f.y) ^ 5 = 1 ∧
      (r'⁻¹ * n.t * r' = f.w * f.u * n.v ∨
        r'⁻¹ * n.t * r' = f.w * f.u * n.v * z) ∧
      r'⁻¹ * n.v * r' = f.u * n.v := by
  rcases hv with hv | hv
  · exact ⟨r, hrH, hrT, hr, hry, ht, hv⟩
  · have hb := f.local_mem_sylow.2.2.2.2.2.2.1
    have hby := (Tits.parrottCommutator_eq_one_iff _ _).mp f.eq18_by
    obtain ⟨hH, hT, hsq, hfifth⟩ := f.seed_conjugate r f.b hrH hrT hr hry hb hby
    refine ⟨f.b⁻¹ * r * f.b, hH, hT, hsq, hfifth, ?_, ?_⟩
    · rw [rc_conjugate f.comm_bt]
      rcases ht with ht | ht
      · exact Or.inr (ht ▸ f.b_images.1)
      · apply Or.inl
        rw [ht, rc_mul, f.b_images.1, rc_fixed f.comm_zb.symm,
          mul_assoc, ← pow_two, f.z_sq, mul_one]
    · have hbv : Commute f.b n.v := by rw [← f.eq03_b]; exact Commute.self_pow _ _
      rw [rc_conjugate hbv, hv, rc_mul, f.b_images.2, rc_fixed f.comm_zb.symm,
        mul_assoc, ← pow_two, f.z_sq, mul_one]

/-- Correct both central factors by conjugations fixing y. The entire supplied
Sylow frame is unchanged. -/
public theorem normalize_t_v_central_factors (r : G)
    (hrH : r ∈ centralizer ({z} : Set G)) (hrT : r ∉ e.sylow)
    (hr : r ^ 2 = 1) (hry : (r * f.y) ^ 5 = 1)
    (ht : r⁻¹ * n.t * r = f.w * f.u * n.v ∨
      r⁻¹ * n.t * r = f.w * f.u * n.v * z)
    (hv : r⁻¹ * n.v * r = f.u * n.v ∨
      r⁻¹ * n.v * r = f.u * n.v * z) :
    ∃ r' : G, r' ∈ centralizer ({z} : Set G) ∧ r' ∉ e.sylow ∧
      r' ^ 2 = 1 ∧ (r' * f.y) ^ 5 = 1 ∧
      r'⁻¹ * n.t * r' = f.w * f.u * n.v * z ∧
      r'⁻¹ * n.v * r' = f.u * n.v := by
  obtain ⟨r', hH, hT, hsq, hfifth, ht', hv'⟩ :=
    f.normalize_v r hrH hrT hr hry ht hv
  rcases ht' with ht' | ht'
  · have ha := f.local_mem_sylow.2.2.2.2.2.1
    have hay := ((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq06_ya).symm
    obtain ⟨hH', hT', hsq', hfifth'⟩ :=
      f.seed_conjugate r' f.a hH hT hsq hfifth ha hay
    refine ⟨f.a⁻¹ * r' * f.a, hH', hT', hsq', hfifth', ?_, ?_⟩
    · rw [rc_conjugate f.comm_at, ht', f.a_images.1]
    · rw [rc_conjugate f.comm_av, hv', f.a_images.2]
  · exact ⟨r', hH, hT, hsq, hfifth, ht', hv'⟩

private theorem central_factor_alternatives [Finite G]
    (h : ParrottCentralizerHypotheses z) (q g : G)
    (hm : q⁻¹ * g ∈ zpowers z) : g = q ∨ g = q * z := by
  classical
  have hh : q⁻¹ * g = 1 ∨ q⁻¹ * g = z := by
    rw [mem_zpowers_iff_mem_range_orderOf, h.involution] at hm
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hm
    have hi2 : i < 2 := Finset.mem_range.mp hi
    interval_cases i
    · exact Or.inl (by simpa using heq.symm)
    · exact Or.inr (by simpa using heq.symm)
  rcases hh with hh | hh
  · exact Or.inl (inv_mul_eq_one.mp hh).symm
  · right
    calc
      g = q * (q⁻¹ * g) := by group
      _ = q * z := by rw [hh]

/-- The geometric input need only determine the two images modulo the
original center. Central-factor correction preserves the supplied frame. -/
public theorem normalize_t_v_mod_center [Finite G]
    (h : ParrottCentralizerHypotheses z) (r : G)
    (hrH : r ∈ centralizer ({z} : Set G)) (hrT : r ∉ e.sylow)
    (hr : r ^ 2 = 1) (hry : (r * f.y) ^ 5 = 1)
    (ht : (f.w * f.u * n.v)⁻¹ * (r⁻¹ * n.t * r) ∈ zpowers z)
    (hv : (f.u * n.v)⁻¹ * (r⁻¹ * n.v * r) ∈ zpowers z) :
    ∃ r' : G, r' ∈ centralizer ({z} : Set G) ∧ r' ∉ e.sylow ∧
      r' ^ 2 = 1 ∧ (r' * f.y) ^ 5 = 1 ∧
      r'⁻¹ * n.t * r' = f.w * f.u * n.v * z ∧
      r'⁻¹ * n.v * r' = f.u * n.v := by
  exact f.normalize_t_v_central_factors r hrH hrT hr hry
    (central_factor_alternatives h _ _ ht) (central_factor_alternatives h _ _ hv)

/-- Select an outer involution with the prescribed elementary action.  The
core-orientation theorem first chooses a seed whose action on the core
abelianization is oriented; duality transfers that action to the two
elementary generators modulo `⟨z⟩`; the central-factor correction then gives
the exact equations (20) and (21).  The supplied Sylow frame is retained
literally, so the witness is `f` itself. -/
public theorem exists_outer_involution_elementary_action
    (f : ParrottSylowGeneratorData n) [Finite G] [IsSimpleGroup G]
    (_hns : ¬ Group.IsSolvable G) (_hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z) :
    ∃ f' : ParrottSylowGeneratorData n, ∃ r : G,
      r ∈ centralizer ({z} : Set G) ∧ r ∉ e.sylow ∧ r ^ 2 = 1 ∧
      (r * f'.y) ^ 5 = 1 ∧
      r⁻¹ * n.t * r = f'.w * f'.u * n.v * z ∧
      r⁻¹ * n.v * r = f'.u * n.v := by
  obtain ⟨r, hrH, hrT, hr2, hry, hra, hrb, hrc, hrd⟩ :=
    f.exists_outer_involution_core_action h
  obtain ⟨htZ, hvZ⟩ :=
    f.t_v_conj_mod_center_of_core_action h r hrH hr2 hra hrb hrc hrd
  obtain ⟨r', hrH', hrT', hr2', hry', ht', hv'⟩ :=
    f.normalize_t_v_mod_center h r hrH hrT hr2 hry htZ hvZ
  exact ⟨f, r', hrH', hrT', hr2', hry', ht', hv'⟩

end ParrottSylowGeneratorData
end Stellmacher.Recognition
