module

public import Stellmacher.Recognition.Parrott.CentralizerActionData
public import Theory.GroupTheory.InvolutionOddProduct
public import Theory.GroupTheory.Involution.OddRotation

/-!
# Seeds and completion for Parrott's centralizer involution

For the actual centralizer H=C_G(z), the supplied Sylow subgroup T has
index five. Consequently every element of H outside T generates H with T.
On a normalized Sylow frame, involutivity and equations (20) and (21)
force both equations (22). These reductions isolate the geometric selection
of the involution from the algebraic completion of its action.

The normalized relations give [u,y]=t, which puts y outside the two-core.
The odd-rotation theorem then supplies an inverted element q of order five.
The element qy is an involution outside T, conjugate to y, and generates
H together with T. Selecting such an involution with the required images
of t,v, and identifying the global class of y, remain separate geometric
steps; this module does not yet assert the full existence theorem.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed pp.680–681, the centralizer-generator paragraph through (22).
-/

open Subgroup
open scoped commutatorElement

namespace Stellmacher.Recognition

variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

/-- The prime index of the supplied Sylow subgroup gives generation of the
actual centralizer by any element outside that Sylow subgroup. -/
public theorem ParrottSecondElementaryData.centralizer_generated_of_not_mem_sylow
    (e : ParrottSecondElementaryData z) [Finite G]
    (h : ParrottCentralizerHypotheses z) (r : G)
    (hrH : r ∈ centralizer ({z} : Set G)) (hrT : r ∉ e.sylow) :
    (e.sylow : Subgroup G) ⊔ zpowers r = centralizer ({z} : Set G) := by
  let H := centralizer ({z} : Set G)
  let L : Subgroup G := (e.sylow : Subgroup G) ⊔ zpowers r
  have hTL : (e.sylow : Subgroup G) ≤ L := le_sup_left
  have hLH : L ≤ H := sup_le e.sylow_le_centralizer (zpowers_le.mpr hrH)
  have hTH : (e.sylow : Subgroup G).relIndex H = 5 := by
    have hc := relIndex_mul_relIndex (⊥ : Subgroup G) (e.sylow : Subgroup G)
      H bot_le e.sylow_le_centralizer
    rw [relIndex_bot_left, relIndex_bot_left, e.sylow_card h,
      (h.card_and_solvable z).1] at hc
    omega
  have hmul := relIndex_mul_relIndex (e.sylow : Subgroup G) L H hTL hLH
  rw [hTH] at hmul
  have hnotone : (e.sylow : Subgroup G).relIndex L ≠ 1 := by
    intro heq
    exact hrT ((relIndex_eq_one.mp heq) (mem_sup_right (mem_zpowers r)))
  have hidx : (e.sylow : Subgroup G).relIndex L = 5 :=
    ((Nat.dvd_prime Nat.prime_five).mp ⟨_, hmul.symm⟩).resolve_left hnotone
  have hLHidx : L.relIndex H = 1 := by rw [hidx] at hmul; omega
  exact le_antisymm hLH (relIndex_eq_one.mp hLHidx)

private theorem conj_twice_of_sq {r : G} (hr : r ^ 2 = 1) (g : G) :
    r⁻¹ * (r⁻¹ * g * r) * r = g := by
  have hrr : r * r = 1 := by simpa only [pow_two] using hr
  have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_right hrr
  rw [hri]
  calc
    r * (r * g * r) * r = (r * r) * g * (r * r) := by group
    _ = g := by rw [hrr]; simp

private theorem conj_mul (r a b : G) :
    r⁻¹ * (a * b) * r = (r⁻¹ * a * r) * (r⁻¹ * b * r) := by group

namespace ParrottSylowGeneratorData

variable (f : ParrottSylowGeneratorData n)

/-- The first part of equation (22) is forced by (21) and r²=1. -/
public theorem u_conj_eq_of_v_conj (r : G) (hr : r ^ 2 = 1)
    (hv : r⁻¹ * n.v * r = f.u * n.v) :
    r⁻¹ * f.u * r = f.u := by
  have hvv := conj_twice_of_sq hr n.v
  rw [hv, conj_mul, hv] at hvv
  have huu : f.u * f.u = 1 := by simpa only [pow_two] using f.u_sq
  apply mul_right_cancel (b := f.u)
  apply mul_right_cancel (b := n.v)
  simpa only [mul_assoc, huu, one_mul] using hvv

/-- The remaining part of equation (22) follows from the two prescribed
images of t and v, with the original z,t,v held fixed. -/
public theorem w_conj_eq_of_t_v_conj (r : G) (hr : r ^ 2 = 1)
    (hz : Commute z r)
    (ht : r⁻¹ * n.t * r = f.w * f.u * n.v * z)
    (hv : r⁻¹ * n.v * r = f.u * n.v) :
    r⁻¹ * f.w * r = n.v * n.t * z := by
  have hu := f.u_conj_eq_of_v_conj r hr hv
  have hzconj : r⁻¹ * z * r = z := by rw [mul_assoc, hz.eq]; simp
  have htt := conj_twice_of_sq hr n.t
  rw [ht, conj_mul, conj_mul, conj_mul, hu, hv, hzconj] at htt
  have huu : f.u * f.u = 1 := by simpa only [pow_two] using f.u_sq
  have hvv : n.v * n.v = 1 := by simpa only [pow_two] using f.v_sq
  have hzz : z * z = 1 := by simpa only [pow_two] using f.z_sq
  have heq : (r⁻¹ * f.w * r) * (n.v * z) = n.t := by
    simpa only [mul_assoc, ← mul_assoc f.u f.u, huu, one_mul] using htt
  apply mul_right_cancel (b := n.v * z)
  rw [heq]
  calc
    n.t = n.v * (n.v * n.t) * (z * z) := by
      rw [← mul_assoc n.v n.v, hvv, hzz]; simp
    _ = n.v * (n.t * n.v) * (z * z) := by rw [f.comm_tv.eq]
    _ = n.v * n.t * (n.v * z) * z := by group
    _ = n.v * n.t * (z * n.v) * z := by rw [f.comm_zv.eq]
    _ = (n.v * n.t * z) * (n.v * z) := by group

/-- A fifth-power relation puts the two square-one generators in the
same conjugacy class. The global class of y is supplied separately. -/
public theorem isConj_y_of_fifth_power (r : G) (hr : r ^ 2 = 1)
    (hry : (r * f.y) ^ 5 = 1) : IsConj r f.y := by
  exact isConj_of_involutions_odd_product r f.y hr f.y_sq
    ((by decide : Odd 5).of_dvd_nat (orderOf_dvd_of_pow_eq_one hry))

/-- Complete all involution-stage fields once the geometric choice supplies
the two images (20)–(21), the fifth-power relation and the class of y.
Every inherited Sylow-frame field is preserved literally. -/
public theorem centralizer_involution_of_t_v_conj [Finite G]
    (h : ParrottCentralizerHypotheses z) (hyz : IsConj f.y z)
    (r : G) (hrH : r ∈ centralizer ({z} : Set G)) (hrT : r ∉ e.sylow)
    (hr : r ^ 2 = 1) (hry : (r * f.y) ^ 5 = 1)
    (ht : r⁻¹ * n.t * r = f.w * f.u * n.v * z)
    (hv : r⁻¹ * n.v * r = f.u * n.v) :
    Nonempty (ParrottCentralizerInvolutionData n) := by
  have hrz := (f.isConj_y_of_fifth_power r hr hry).trans hyz
  have hcomm : Commute z r := (mem_centralizer_singleton_iff.mp hrH).symm
  refine ⟨{ toParrottSylowGeneratorData := f
            r := r
            centralizer_generators := e.centralizer_generated_of_not_mem_sylow h r hrH hrT
            r_order := orderOf_eq_prime_iff.mpr
              ⟨hr, fun heq => hrT (heq ▸ (e.sylow : Subgroup G).one_mem)⟩
            r_conjugate := hrz
            comm_zr := hcomm
            eq20_r := hr
            eq20_ry := hry
            eq20_tr := ht
            eq21_vr := hv
            eq22_ur := f.u_conj_eq_of_v_conj r hr hv
            eq22_wr := f.w_conj_eq_of_t_v_conj r hr hcomm ht hv }⟩

private theorem right_conj_of_commutator {a b c : G}
    (h : Tits.parrottCommutator a b = c) (hc : c ^ 2 = 1) :
    a⁻¹ * b * a = b * c := by
  have hswap := (Tits.parrottCommutator_eq_iff _ _ _).mp h
  have hcc : c * c = 1 := by simpa only [pow_two] using hc
  have heq := congrArg (fun g : G => a⁻¹ * g * c) hswap
  simpa only [mul_assoc, inv_mul_cancel_left, hcc, mul_one] using heq.symm

/-- Conjugation by the prescribed y moves u by the original t. -/
public theorem y_conj_u : f.y⁻¹ * f.u * f.y = f.u * n.t := by
  have hxu := right_conj_of_commutator f.eq01_xu f.v_sq
  have hxv := right_conj_of_commutator f.eq01_xv f.t_sq
  have hvv : n.v * n.v = 1 := by simpa only [pow_two] using f.v_sq
  have hx2 : (f.x ^ 2)⁻¹ * f.u * f.x ^ 2 = f.u * n.t := by
    calc
      _ = f.x⁻¹ * (f.x⁻¹ * f.u * f.x) * f.x := by simp only [pow_two]; group
      _ = f.x⁻¹ * (f.u * n.v) * f.x := by rw [hxu]
      _ = (f.x⁻¹ * f.u * f.x) * (f.x⁻¹ * n.v * f.x) := by group
      _ = (f.u * n.v) * (n.v * n.t) := by rw [hxu, hxv]
      _ = f.u * n.t := by simp only [mul_assoc, ← mul_assoc n.v n.v, hvv, one_mul]
  rw [f.eq04] at hx2
  have hz : z⁻¹ * f.u * z = f.u := by rw [mul_assoc, f.comm_zu.symm.eq]; simp
  calc
    f.y⁻¹ * f.u * f.y = f.y⁻¹ * (z⁻¹ * f.u * z) * f.y := by rw [hz]
    _ = (z * f.y)⁻¹ * f.u * (z * f.y) := by group
    _ = (f.y * z)⁻¹ * f.u * (f.y * z) := by rw [f.comm_zy.eq]
    _ = f.u * n.t := hx2

/-- The prescribed y lies outside the original two-core: its commutator
with u is t, whereas core commutators with the derived core lie in ⟨z⟩. -/
public theorem y_not_mem_core [Finite G] (h : ParrottCentralizerHypotheses z) :
    f.y ∉ (pCore 2 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  have huE : f.u ∈ E := by
    change f.u ∈ (commutator J).map (H.subtype.comp J.subtype)
    rw [← f.derived_basis]
    exact subset_closure (by simp)
  obtain ⟨uJ, huD, hu⟩ := huE
  intro hy
  obtain ⟨yH, hyJ, hy⟩ := hy
  let yJ : J := ⟨yH, hyJ⟩
  obtain ⟨hZ, _, _, _, hupper, _, _, _⟩ := parrott_centralizer_structure z h
  have huU : uJ ∈ Subgroup.upperCentralSeries J 2 := hupper ▸ huD
  have hc : ⁅uJ, yJ⁆ ∈ center J := by
    simpa only [Subgroup.upperCentralSeries_one] using
      Subgroup.mem_upperCentralSeries_succ_iff.mp huU yJ
  have hct : ⁅f.u, f.y⁆ = n.t := by
    have hui : f.u⁻¹ = f.u := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using f.u_sq)
    have hyi : f.y⁻¹ = f.y := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using f.y_sq)
    have hconj := f.y_conj_u
    rw [hyi] at hconj
    rw [commutatorElement_def, hui, hyi]
    calc
      f.u * f.y * f.u * f.y = f.u * (f.y * f.u * f.y) := by group
      _ = f.u * (f.u * n.t) := by rw [hconj]
      _ = n.t := by rw [← mul_assoc, ← pow_two, f.u_sq, one_mul]
  apply n.t_not_mem_zpowers
  rw [← hZ]
  refine ⟨⁅uJ, yJ⁆, hc, ?_⟩
  change (H.subtype.comp J.subtype) ⁅uJ, yJ⁆ = n.t
  rw [map_commutatorElement, hu]
  change ⁅f.u, (yH : G)⁆ = n.t
  change (yH : G) = f.y at hy
  rw [hy, hct]

/-- The normalized Sylow coordinate y is an actual involution. -/
public theorem y_order [Finite G] (h : ParrottCentralizerHypotheses z) : orderOf f.y = 2 := by
  apply orderOf_eq_prime_iff.mpr
  refine ⟨f.y_sq, ?_⟩
  intro hy
  exact f.y_not_mem_core h (hy ▸ one_mem _)

/-- Extract an actual outer involution conjugate to the prescribed y.
An inverted odd-prime rotation has order five; its product with y supplies
the involution, the fifth-power relation and generation of H with T.
No action on the elementary generators is asserted here. -/
public theorem exists_outer_involution_fifth_power [Finite G]
    (h : ParrottCentralizerHypotheses z) :
    ∃ r : G, r ∈ centralizer ({z} : Set G) ∧ r ∉ e.sylow ∧
      orderOf r = 2 ∧ IsConj r f.y ∧ (r * f.y) ^ 5 = 1 ∧
      (e.sylow : Subgroup G) ⊔ zpowers r = centralizer ({z} : Set G) := by
  let H := centralizer ({z} : Set G)
  let yH : H := ⟨f.y, e.sylow_le_centralizer f.local_mem_sylow.2.2.2.2.2.2.2.2.2.2⟩
  have hy2 : yH ^ 2 = 1 := Subtype.ext f.y_sq
  have hyJ : yH ∉ pCore 2 H := fun hh =>
    f.y_not_mem_core h (mem_map_of_mem H.subtype hh)
  have hyne : yH ≠ 1 := fun hh => hyJ (hh ▸ one_mem _)
  obtain ⟨p, hp, hp2, q, hq, hyq⟩ :=
    BenderSuzuki.involution_outside_twoCore_inverts_odd_prime yH ⟨hyne, hy2⟩ hyJ
  have hpdiv : p ∣ 10240 := by
    rw [← (h.card_and_solvable z).1, ← hq]
    exact orderOf_dvd_natCard q
  have hp5 : p = 5 := by
    rw [show 10240 = 2 ^ 11 * 5 by decide] at hpdiv
    rcases hp.dvd_mul.mp hpdiv with hh | hh
    · have hh' : p ∣ 2 := hp.dvd_of_dvd_pow hh
      rcases (Nat.dvd_prime Nat.prime_two).mp hh' with hh' | hh'
      · exact (hp.ne_one hh').elim
      · exact (hp2 hh').elim
    · exact ((Nat.dvd_prime Nat.prime_five).mp hh).resolve_left hp.ne_one
  have hq5 : orderOf q = 5 := hq.trans hp5
  have hqG5 : orderOf (q : G) = 5 := (Subgroup.orderOf_coe q).trans hq5
  have hyi : yH⁻¹ = yH := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hy2)
  change yH⁻¹ * q * yH = q⁻¹ at hyq
  rw [hyi] at hyq
  let rH : H := q * yH
  have hr2 : rH ^ 2 = 1 := by
    change (q * yH) ^ 2 = 1
    calc
      _ = q * (yH * q * yH) := by simp only [pow_two]; group
      _ = 1 := by rw [hyq, mul_inv_cancel]
  have hry : rH * yH = q := by
    change q * yH * yH = q
    rw [mul_assoc, ← pow_two, hy2, mul_one]
  have hrT : (rH : G) ∉ e.sylow := by
    intro hh
    have hqT : (q : G) ∈ e.sylow := by
      have hh' := (e.sylow : Subgroup G).mul_mem hh
        f.local_mem_sylow.2.2.2.2.2.2.2.2.2.2
      change ((rH * yH : H) : G) ∈ e.sylow at hh'
      simpa only [hry] using hh'
    have hdiv := (e.sylow : Subgroup G).orderOf_dvd_natCard hqT
    rw [hqG5, e.sylow_card h] at hdiv
    norm_num at hdiv
  have hrG2 : (rH : G) ^ 2 = 1 := congrArg Subtype.val hr2
  have hry5 : ((rH : G) * f.y) ^ 5 = 1 := by
    have heq : (rH : G) * f.y = (q : G) := congrArg Subtype.val hry
    rw [heq, ← hqG5, pow_orderOf_eq_one]
  exact ⟨rH, rH.property, hrT,
    orderOf_eq_prime_iff.mpr ⟨hrG2, fun heq => hrT (heq ▸ one_mem _)⟩,
    f.isConj_y_of_fifth_power rH hrG2 hry5, hry5,
    e.centralizer_generated_of_not_mem_sylow h rH rH.property hrT⟩

end ParrottSylowGeneratorData

end Stellmacher.Recognition
