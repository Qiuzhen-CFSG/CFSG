module
public import Stellmacher.Recognition.Parrott.NormalizerCoreSquareRoots
public import Stellmacher.Recognition.Parrott.CentralizerInvolutionSeed

/-!
# Transporting the normalized Sylow root into the original core

For the supplied normalized frame, x belongs to K = O₂(N_G(F)) and lies
outside Ω₁(K), since [x,v] = t ≠ 1. Its square x² = yz is an involution
outside J = O₂(C_G(z)). The existing involution transport carries this
square into E = J′. Apply the same conjugator to x. If the transported
root were outside J, the outer-square bridge would put it in Ω₁(K).
Normality of Ω₁(K) in N_G(F) would then put x there too, a contradiction.

Thus the same normalizer conjugator transports the root into J. This
argument preserves every supplied frame coordinate and does not use the
global involution class of y.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.678, the assertion x ∼_N c* immediately preceding equation (4).
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSylowGeneratorData
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

/-- A normalizer conjugate of the supplied normalized x belongs to the
original two-core. No change of the normalized coordinates is made. -/
public theorem x_conjugate_mem_core (f : ParrottSylowGeneratorData n)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G) :
    ∃ q : normalizer (e.F : Set G), (q : G) * f.x * (q : G)⁻¹ ∈
      (pCore 2 (centralizer ({z} : Set G))).map
        (centralizer ({z} : Set G)).subtype := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  let N := normalizer (e.F : Set G)
  let K := pCore 2 N
  let X := K.map N.subtype
  let U := omega₁ K (p := 2)
  let W := U.map (N.subtype.comp K.subtype)
  have hxX : f.x ∈ X := by
    change f.x ∈ (pCore 2 (normalizer (e.F : Set G))).map
      (normalizer (e.F : Set G)).subtype
    rw [n.core_eq_sylow_centralizer]
    exact ⟨f.local_mem_sylow.2.2.2.2.2.2.2.2.2.1,
      mem_centralizer_singleton_iff.mpr
        ((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq01_xt)⟩
  have hxW : f.x ∉ W := by
    intro hx
    have hWC : W = X ⊓ centralizer
        ((center U).map ((N.subtype.comp K.subtype).comp U.subtype) : Set G) :=
      n.omega_eq_centralizer
    rw [hWC] at hx
    have hv : n.v ∈ (center U).map ((N.subtype.comp K.subtype).comp U.subtype) := by
      have hZ : (center U).map ((N.subtype.comp K.subtype).comp U.subtype) =
          (zpowers z ⊔ zpowers n.t) ⊔ zpowers n.v := n.omega_center_eq
      rw [hZ]
      exact mem_sup_right (mem_zpowers n.v)
    have hc : Commute f.x n.v := (mem_centralizer_iff.mp hx.2 n.v hv).symm
    have ht : n.t = 1 := f.eq01_xv.symm.trans
      ((Tits.parrottCommutator_eq_one_iff _ _).mpr hc)
    have ho := n.t_order
    rw [ht, orderOf_one] at ho
    norm_num at ho
  have hsqJ : f.x ^ 2 ∉ J.map H.subtype := by
    intro hx
    rw [f.eq04] at hx
    exact f.y_not_mem_core h
      ((J.map H.subtype).mul_mem_cancel_right (e.le_core e.z_mem_inf.2) |>.mp hx)
  have hsq2 : (f.x ^ 2) ^ 2 = 1 := by simpa only [← pow_mul] using f.eq01_x
  have hsqOrder : orderOf (f.x ^ 2) = 2 := orderOf_eq_prime hsq2
    (fun heq => hsqJ (heq ▸ (J.map H.subtype).one_mem))
  obtain ⟨q, hq⟩ := e.normalizer_core_involution_transport h hN n.sylow_lt_normalizer
    n.Q n.core_fixed_le_derived (f.x ^ 2) (X.pow_mem hxX 2) hsq2
  let qN : N := q
  have hqE : (qN : G) * f.x ^ 2 * (qN : G)⁻¹ ∈ E :=
    e.outer_involution_normalizer_conjugate_mem_derived h (f.x ^ 2) hsqJ hsqOrder qN hq
  let a := (qN : G) * f.x * (qN : G)⁻¹
  have haX : a ∈ X := by
    obtain ⟨xN, hxN, hex⟩ := hxX
    refine ⟨qN * xN * qN⁻¹, (inferInstance : K.Normal).conj_mem xN hxN qN, ?_⟩
    change (qN : G) * (xN : G) * (qN : G)⁻¹ = a
    change (xN : G) = f.x at hex
    rw [hex]
  have ha2 : a ^ 2 ∈ E := by
    have heq : a ^ 2 = (qN : G) * f.x ^ 2 * (qN : G)⁻¹ :=
      (map_pow (MulAut.conj (qN : G)) f.x 2).symm
    rwa [heq]
  have hNW : N ≤ normalizer (W : Set G) := by
    let V := U.map K.subtype
    let : U.Characteristic := omega₁_characteristic K
    let : V.Normal := ConjAct.normal_of_characteristic_of_normal
    have hh := le_normalizer_map (H := V) N.subtype
    rw [normalizer_eq_top] at hh
    simpa only [← MonoidHom.range_eq_map, range_subtype, V, W, map_map] using hh
  refine ⟨qN, ?_⟩
  by_contra haJ
  have haW : a ∈ W := e.normalizer_core_outer_square_mem_derived_mem_omega h hN
    n.sylow_lt_normalizer a haX ha2 haJ
  exact hxW ((mem_normalizer_iff.mp (hNW qN.property) f.x).mpr haW)
end Stellmacher.Recognition.ParrottSylowGeneratorData
