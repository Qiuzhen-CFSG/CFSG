module

public import Stellmacher.Recognition.Parrott.CentralizerInvolutionSeed
public import Stellmacher.Recognition.Parrott.CoreQuotientAction

/-!
# Seed transport for orientation on the core abelianization

For H=C_G(z), J=O₂(H), and E the ambient image of J′, the normalized
Sylow frame supplies actual involutions a,d outside E. Conjugating an outer
involution seed by any Sylow element centralizing y preserves all seed
conditions, including the actual fifth-power equation. In particular every
power of x gives an admissible conjugate, with the original frame unchanged.

Once aE is sent to dE, involutivity forces dE to be sent back to aE.
The remaining geometric obligations are to select the first image and to
determine the images of bE,cE. This module records the checked transport
lemmas; it does not assert those two unproved selection and rigidity steps.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.680, the centralizer-generator paragraph, and p.681, equation (23).
-/

open Subgroup
open scoped IsMulCommutative

namespace Stellmacher.Recognition
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

namespace ParrottSylowGeneratorData
variable (f : ParrottSylowGeneratorData n)

/-- The four supplied core generators lie in the literal ambient two-core. -/
public theorem core_orientation_mem_core :
    let H := centralizer ({z} : Set G)
    let K := (pCore 2 H).map H.subtype
    f.a ∈ K ∧ f.b ∈ K ∧ f.c ∈ K ∧ f.d ∈ K := by
  dsimp only
  rw [← f.core_generators]
  exact ⟨subset_closure (by simp), subset_closure (by simp),
    subset_closure (by simp), subset_closure (by simp)⟩

/-- All five elementary coordinates belong to the actual derived core. -/
public theorem core_orientation_mem_derived :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    z ∈ E ∧ n.t ∈ E ∧ n.v ∈ E ∧ f.u ∈ E ∧ f.w ∈ E := by
  dsimp only
  rw [← f.derived_basis]
  exact ⟨subset_closure (by simp), subset_closure (by simp),
    subset_closure (by simp), subset_closure (by simp), subset_closure (by simp)⟩

/-- The involutions a,d represent nonidentity cosets in the core abelianization.
Their commutators with w,t respectively are the nonidentity central involution. -/
public theorem core_orientation_not_mem_derived [Finite G]
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    f.a ∉ E ∧ f.d ∉ E := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  let : IsElementaryAbelian 2 (commutator J) :=
    (parrott_centralizer_structure z h).2.2.2.2.2.1
  let : IsMulCommutative E := Subgroup.map_isMulCommutative _ _
  have hcomm {g k : G} (hg : g ∈ E) (hk : k ∈ E) : Commute g k := by
    exact congrArg Subtype.val (mul_comm (⟨g, hg⟩ : E) (⟨k, hk⟩ : E))
  have hzne : z ≠ 1 := by
    intro hz
    have hh := h.involution
    rw [hz, orderOf_one] at hh
    omega
  constructor
  · intro ha
    have hc := (Tits.parrottCommutator_eq_one_iff _ _).mpr
      (hcomm ha f.core_orientation_mem_derived.2.2.2.2)
    exact hzne (f.eq02_aw.symm.trans hc)
  · intro hd
    have hc := (Tits.parrottCommutator_eq_one_iff _ _).mpr
      (hcomm hd f.core_orientation_mem_derived.2.1)
    exact hzne (f.eq03_dt.symm.trans hc)

/-- Conjugations in the Sylow centralizer of y preserve genuine seeds,
including the fifth-power relation in the ambient group. -/
public theorem core_orientation_seed_conjugate (r k : G)
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

/-- The supplied fourth-order coordinate commutes with the prescribed y. -/
public theorem core_orientation_x_commute_y : Commute f.x f.y := by
  have hx : f.x * (f.y * z) = (f.y * z) * f.x := by
    rw [← f.eq04]
    exact (Commute.self_pow f.x 2).eq
  change f.x * f.y = f.y * f.x
  apply mul_right_cancel (b := z)
  calc
    f.x * f.y * z = f.x * (f.y * z) := by group
    _ = (f.y * z) * f.x := hx
    _ = f.y * f.x * z := by rw [mul_assoc, f.comm_zx.eq]; group

/-- Every power of x transports an actual seed without changing any frame field. -/
public theorem core_orientation_seed_xpow (r : G) (i : ℕ)
    (hrH : r ∈ centralizer ({z} : Set G)) (hrT : r ∉ e.sylow)
    (hr : r ^ 2 = 1) (hry : (r * f.y) ^ 5 = 1) :
    (f.x ^ i)⁻¹ * r * f.x ^ i ∈ centralizer ({z} : Set G) ∧
      (f.x ^ i)⁻¹ * r * f.x ^ i ∉ e.sylow ∧
      ((f.x ^ i)⁻¹ * r * f.x ^ i) ^ 2 = 1 ∧
      (((f.x ^ i)⁻¹ * r * f.x ^ i) * f.y) ^ 5 = 1 := by
  exact f.core_orientation_seed_conjugate r (f.x ^ i) hrH hrT hr hry
    ((e.sylow : Subgroup G).pow_mem f.local_mem_sylow.2.2.2.2.2.2.2.2.2.1 i)
    (f.core_orientation_x_commute_y.pow_left i)

/-- Conjugation by the centralizer preserves the literal ambient derived core. -/
public theorem core_orientation_conj_mem_derived (r g : G)
    (hr : r ∈ centralizer ({z} : Set G))
    (hg : g ∈ (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype)) :
    r⁻¹ * g * r ∈ (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype) := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let DH := (commutator J).map J.subtype
  let rH : H := ⟨r, hr⟩
  obtain ⟨gJ, hgJ, hgg⟩ := hg
  have hgH : (gJ : H) ∈ DH := mem_map_of_mem J.subtype hgJ
  have hh := (inferInstance : DH.Normal).conj_mem (gJ : H) hgH rH⁻¹
  have hm := mem_map_of_mem H.subtype hh
  rw [map_map] at hm
  simp only [inv_inv] at hm
  have hgg' : ((gJ : H) : G) = g := hgg
  change r⁻¹ * ((gJ : H) : G) * r ∈
    (commutator J).map (H.subtype.comp J.subtype) at hm
  rw [hgg'] at hm
  exact hm

/-- Involutivity forces the reverse core-coset image dE ↦ aE. -/
public theorem core_orientation_d_image_of_a_image (r : G)
    (hrH : r ∈ centralizer ({z} : Set G)) (hr : r ^ 2 = 1)
    (ha : f.d⁻¹ * (r⁻¹ * f.a * r) ∈
      (commutator (pCore 2 (centralizer ({z} : Set G)))).map
        ((centralizer ({z} : Set G)).subtype.comp
          (pCore 2 (centralizer ({z} : Set G))).subtype)) :
    f.a⁻¹ * (r⁻¹ * f.d * r) ∈
      (commutator (pCore 2 (centralizer ({z} : Set G)))).map
        ((centralizer ({z} : Set G)).subtype.comp
          (pCore 2 (centralizer ({z} : Set G))).subtype) := by
  have hh := core_orientation_conj_mem_derived r _ hrH ha
  have hrr : r * r = 1 := by simpa only [pow_two] using hr
  have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_right hrr
  have heq : r⁻¹ * (f.d⁻¹ * (r⁻¹ * f.a * r)) * r =
      (r⁻¹ * f.d * r)⁻¹ * f.a := by
    rw [hri]
    calc
      _ = r * f.d⁻¹ * (r * f.a * (r * r)) := by group
      _ = r * f.d⁻¹ * r * f.a := by rw [hrr]; group
      _ = _ := by rw [mul_inv_rev, mul_inv_rev, hri]; group
  rw [heq] at hh
  simpa only [mul_inv_rev, inv_inv] using inv_mem hh

end ParrottSylowGeneratorData
end Stellmacher.Recognition
