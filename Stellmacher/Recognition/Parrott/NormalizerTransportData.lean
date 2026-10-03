module

public import Stellmacher.Recognition.Parrott.NormalizerGeneratorSeed

/-!
# The transport stage of Parrott's normalizer selection

The first stage chooses an involution carrying y to wuvz, and consequently
t to z and v to vtz. The remaining square-root argument refines that choice
without changing the supplied centralizer coordinates. This intermediate
interface records the first stage without asserting its existence.

The supporting calculations identify the G-class of y using (ry)⁵ = 1 and
identify the common square of xˢ and caw. They use only the supplied frame;
in particular, no later normalizer equations enter these calculations.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§3, printed pp.681–682, “Generators and relations for N”.
-/

open Subgroup

namespace Stellmacher.Recognition

variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

/-- The involution transport preceding the square-root normalization.
Existence is a separate geometric assertion. -/
public structure ParrottNormalizerTransportData (f : ParrottCentralizerGeneratorData n) where
  s : G
  mem_normalizer : s ∈ normalizer (e.F : Set G)
  sq : s ^ 2 = 1
  t_conj : s⁻¹ * n.t * s = z
  v_conj : s⁻¹ * n.v * s = n.v * n.t * z
  y_conj : s⁻¹ * f.y * s = f.w * f.u * n.v * z

namespace ParrottCentralizerGeneratorData

variable (f : ParrottCentralizerGeneratorData n)

/-- The fifth-power relation places y in the class of z. -/
public theorem y_isConj_z : IsConj f.y z := by
  have hodd : Odd (orderOf (f.r * f.y)) :=
    (by decide : Odd 5).of_dvd_nat (orderOf_dvd_of_pow_eq_one f.eq20_ry)
  exact (isConj_of_involutions_odd_product f.r f.y f.eq20_r f.y_sq hodd).symm.trans
    f.r_conjugate

/-- The intended image of y has the same involution class. -/
public theorem y_isConj_wuvz : IsConj f.y (f.w * f.u * n.v * z) := by
  obtain ⟨q, hq⟩ := n.three_conjugates_z_t
  have hzt : IsConj z n.t := isConj_iff.mpr ⟨((q : normalizer (e.F : Set G)) : G), hq⟩
  have htr : IsConj n.t (f.w * f.u * n.v * z) :=
    isConj_iff.mpr ⟨f.r⁻¹, by simpa only [inv_inv] using f.eq20_tr⟩
  exact f.y_isConj_z.trans (hzt.trans htr)

end ParrottCentralizerGeneratorData

namespace ParrottSylowGeneratorData

variable (f : ParrottSylowGeneratorData n)

private theorem tail {p q o : G} (hp : p * q = o) (k : G) :
    p * (q * k) = o * k := by rw [← mul_assoc, hp]

/-- The distinguished root caw squares to wuvtz. -/
public theorem caw_sq : (f.c * f.a * f.w) ^ 2 = f.w * f.u * n.v * n.t * z := by
  have ac := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq12_ac
  have aw := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq02_aw
  have cw := (Tits.parrottCommutator_eq_one_iff _ _).mp f.eq09_cw
  have wa : f.w * f.a = f.a * f.w * z := by
    rw [aw]
    simp only [mul_assoc, ← pow_two, f.z_sq, mul_one]
  have aa : f.a * f.a = 1 := by simpa only [pow_two] using f.a_sq
  have ww : f.w * f.w = 1 := by simpa only [pow_two] using f.w_sq
  have cc : f.c * f.c = f.w * f.u := by simpa only [pow_two] using f.eq13
  simp only [pow_two, mul_assoc, tail cw.symm.eq, tail ac, tail wa,
    tail f.comm_av.symm.eq, tail f.comm_at.symm.eq, tail aa,
    tail cc, f.comm_zw.eq, tail ww, one_mul]

/-- The root x belongs to the actual normalizer core. -/
public theorem x_mem_normalizer_core :
    f.x ∈ (pCore 2 (normalizer (e.F : Set G))).map (normalizer (e.F : Set G)).subtype := by
  rw [n.core_eq_sylow_centralizer]
  rcases f.local_mem_sylow with ⟨_, _, _, _, _, _, _, _, _, hx, _⟩
  refine ⟨hx, mem_centralizer_singleton_iff.mpr ?_⟩
  exact ((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq01_xt).eq

/-- The root x is outside the omega subgroup: its action on v is nontrivial. -/
public theorem x_not_mem_normalizer_omega :
    f.x ∉ (omega₁ (pCore 2 (normalizer (e.F : Set G))) (p := 2)).map
      ((normalizer (e.F : Set G)).subtype.comp (pCore 2 (normalizer (e.F : Set G))).subtype) := by
  intro hx
  rw [n.omega_eq_centralizer] at hx
  have hv : n.v ∈ (center (omega₁ (pCore 2 (normalizer (e.F : Set G))) (p := 2))).map
      (((normalizer (e.F : Set G)).subtype.comp
        (pCore 2 (normalizer (e.F : Set G))).subtype).comp
          (omega₁ (pCore 2 (normalizer (e.F : Set G))) (p := 2)).subtype) := by
    rw [n.omega_center_eq]
    exact mem_sup_right (mem_zpowers n.v)
  have hc : Commute f.x n.v := (mem_centralizer_iff.mp hx.2 n.v hv).symm
  have ht : n.t = 1 := f.eq01_xv.symm.trans
    ((Tits.parrottCommutator_eq_one_iff _ _).mpr hc)
  have ho := n.t_order
  rw [ht, orderOf_one] at ho
  norm_num at ho

/-- The root x has order four, since every square-one core element lies in omega. -/
public theorem x_order : orderOf f.x = 4 := by
  have hnot : f.x ^ 2 ≠ 1 := fun hh => f.x_not_mem_normalizer_omega
    (e.normalizer_core_square_one_mem_omega f.x f.x_mem_normalizer_core hh)
  exact orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using hnot) f.eq01_x

end ParrottSylowGeneratorData

namespace ParrottNormalizerTransportData

variable {f : ParrottCentralizerGeneratorData n} (k : ParrottNormalizerTransportData f)

/-- An involution interchanging t and z also carries z back to t. -/
public theorem z_conj : k.s⁻¹ * z * k.s = n.t := by
  have hi : k.s⁻¹ = k.s := inv_eq_of_mul_eq_one_right (by
    simpa only [pow_two] using k.sq)
  have hh := congrArg (fun g : G => k.s * g * k.s⁻¹) k.t_conj
  have he : n.t = k.s * z * k.s⁻¹ := by
    simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left,
      mul_inv_cancel, mul_one] using hh
  simpa only [hi] using he.symm

/-- Transport fixes the square-root fiber that must be normalized. -/
public theorem x_conj_sq :
    (k.s⁻¹ * f.x * k.s) ^ 2 = f.w * f.u * n.v * n.t * z := by
  calc
    (k.s⁻¹ * f.x * k.s) ^ 2 = k.s⁻¹ * f.x ^ 2 * k.s := by simp only [pow_two]; group
    _ = (k.s⁻¹ * f.y * k.s) * (k.s⁻¹ * z * k.s) := by rw [f.eq04]; group
    _ = (f.w * f.u * n.v * z) * n.t := by rw [k.y_conj, k.z_conj]
    _ = f.w * f.u * n.v * n.t * z := by rw [mul_assoc, f.comm_zt.eq, ← mul_assoc]

/-- The transported root and the proposed representative have equal squares. -/
public theorem x_conj_sq_eq_caw_sq :
    (k.s⁻¹ * f.x * k.s) ^ 2 = (f.c * f.a * f.w) ^ 2 :=
  k.x_conj_sq.trans f.toParrottSylowGeneratorData.caw_sq.symm

/-- Once the two remaining image alternatives hold, the transport is a seed. -/
public def toSeed
    (ha : k.s⁻¹ * f.a * k.s = f.u ∨ k.s⁻¹ * f.a * k.s = f.u * z)
    (hx : k.s⁻¹ * f.x * k.s = f.c * f.a * f.w ∨
      k.s⁻¹ * f.x * k.s = f.c * f.a * f.w * n.t * z) : ParrottNormalizerSeedData f where
  s := k.s
  mem_normalizer := k.mem_normalizer
  sq := k.sq
  t_conj := k.t_conj
  v_conj := k.v_conj
  y_conj := k.y_conj
  a_conj := ha
  x_conj := hx

end ParrottNormalizerTransportData

end Stellmacher.Recognition
