module

public import Stellmacher.Recognition.Parrott.SylowSeedOuterGeometry
public import Stellmacher.Recognition.Parrott.NormalizerCoreSquareRoots
public import Stellmacher.Recognition.Parrott.CoreSquareFusion
public import Stellmacher.Recognition.Parrott.OuterInvolutionClasses
public import Stellmacher.Recognition.Parrott.FusionOutsideDerived

/-!
# Separation of the seed's outer involution and its central twist

The seed root x lies in the two-core of the second normalizer but outside its
omega subgroup. Transporting its outer involutory square into the original
derived core therefore transports x into the original two-core. The square
fusion theorem identifies x² with the v-class. The two-representative cover
then identifies x²z with the z-class, since a z-conjugate occurs outside the
original two-core. These distinct global classes cannot fuse in C_G(z).

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed pp.674 and 678, especially the argument preceding equation (4).
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSylowSeedData

variable {G : Type*} [Group G] [Finite G] {z : G}
  {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}
variable (f : ParrottSylowSeedData n false)

/-- A normalizer conjugate of the seed root lies in the original two-core. -/
public theorem x_conjugate_mem_original_core
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
  have hxX : f.x ∈ X := f.x_mem_normalizer_core
  have hxW : f.x ∉ W := by
    intro hx
    have hWC : W = X ⊓ centralizer
        ((center U).map ((N.subtype.comp K.subtype).comp U.subtype) : Set G) :=
      n.omega_eq_centralizer
    rw [hWC] at hx
    have hv : n.v ∈ (center U).map ((N.subtype.comp K.subtype).comp U.subtype) := by
      rw [n.omega_center_eq]
      exact mem_sup_right (mem_zpowers n.v)
    have hc : Commute f.x n.v := (mem_centralizer_iff.mp hx.2 n.v hv).symm
    have ht : n.t = 1 := f.relations.eq01_xv.symm.trans
      ((Tits.parrottCommutator_eq_one_iff _ _).mpr hc)
    have ho := n.t_order
    rw [ht, orderOf_one] at ho
    norm_num at ho
  have hsqJ : f.x ^ 2 ∉ J.map H.subtype := f.square_not_mem_core h
  have hsq2 : (f.x ^ 2) ^ 2 = 1 := by
    simpa only [← pow_mul] using f.relations.eq01_x
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

/-- Every noncentral square in the original core is in the supplied v-class. -/
public theorem core_square_isConj_v (f : ParrottSylowSeedData n false)
    (h : ParrottCentralizerHypotheses z) :
    ∀ a : G, a ∈ (pCore 2 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype →
      a ^ 2 ∉ zpowers z → IsConj (a ^ 2) n.v := by
  exact parrott_core_square_isConj_v_of_initial_elements h f.a f.b f.w
    (by rw [← f.core_generators]; exact subset_closure (by simp))
    (by rw [← f.core_generators]; exact subset_closure (by simp))
    (by rw [← f.derived_basis]; exact subset_closure (by simp))
    f.relations.a_sq f.relations.eq03_b f.relations.eq02_aw

/-- The seed square is in the v-class, before equations (17)-(19). -/
public theorem square_isConj_v
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G) :
    IsConj (f.x ^ 2) n.v := by
  let N := normalizer (e.F : Set G)
  let K := pCore 2 N
  let ZK := (center K).map (N.subtype.comp K.subtype)
  obtain ⟨q, hq⟩ := f.x_conjugate_mem_original_core h hN
  let α := MulAut.conj (q : G)
  have hsq : (α f.x) ^ 2 ∉ zpowers z := by
    intro hs
    have hsZ : α (f.x ^ 2) ∈ ZK := by
      rw [map_pow]
      exact (zpowers_le.mpr e.z_mem_normalizer_core_center) hs
    have hxZ : f.x ^ 2 ∈ ZK :=
      (mem_normalizer_iff.mp (e.normalizer_core_centers_normalized.1 q.property)
        (f.x ^ 2)).mpr hsZ
    exact f.square_not_mem_core h (e.le_core (e.normalizer_core_center_le hxZ))
  have hv : IsConj ((α f.x) ^ 2) n.v := f.core_square_isConj_v h _ hq hsq
  have hc : IsConj (f.x ^ 2) ((α f.x) ^ 2) := by
    apply isConj_iff.mpr
    exact ⟨(q : G), (map_pow α f.x 2)⟩
  exact hc.trans hv

variable [IsSimpleGroup G]

/-- The central twist of the seed square is in the z-class. -/
public theorem square_mul_z_isConj_z
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z) : IsConj (f.x ^ 2 * z) z := by
  have hxv := f.square_isConj_v h hN
  obtain ⟨u, hu2, huH, huE, hzu⟩ := parrott_fusion_outside_derived hns hN z h
  have huJ : u ∉ (pCore 2 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype := by
    intro huJ
    obtain ⟨l, hl⟩ := n.original_core_fusion u huJ huE hu2
    exact n.not_isConj (hzu.trans (isConj_iff.mpr ⟨(l : G), hl⟩).symm)
  obtain ⟨a, ha⟩ := parrott_outer_involution_classes z h (f.x ^ 2 * z) u
    (e.sylow_le_centralizer f.square_mul_z_mem_sylow)
    (f.square_mul_z_not_mem_core h) (f.square_mul_z_order h) huH huJ hu2
  rcases ha with ha | ha
  · exact (hzu.trans (isConj_iff.mpr ⟨(a : G), ha⟩)).symm
  · have htwist : (f.x ^ 2 * z) * z = f.x ^ 2 := by
      rw [mul_assoc, ← pow_two, show z ^ 2 = 1 from h.involution ▸ pow_orderOf_eq_one z]
      simp
    exact (n.not_isConj
      ((hzu.trans (isConj_iff.mpr ⟨(a : G), ha⟩)).trans (by simpa only [htwist] using hxv))).elim

/-- No element of C_G(z) fuses the two outer seed involutions. -/
public theorem square_mul_z_nonfusion
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z) :
    ∀ q : centralizer ({z} : Set G),
      (q : G) * (f.x ^ 2 * z) * (q : G)⁻¹ ≠ (f.x ^ 2 * z) * z := by
  intro q hq
  have htwist : (f.x ^ 2 * z) * z = f.x ^ 2 := by
    rw [mul_assoc, ← pow_two, show z ^ 2 = 1 from h.involution ▸ pow_orderOf_eq_one z]
    simp
  exact n.not_isConj ((f.square_mul_z_isConj_z hns hN h).symm.trans
    ((isConj_iff.mpr ⟨(q : G), by simpa only [htwist] using hq⟩).trans
      (f.square_isConj_v h hN)))

end Stellmacher.Recognition.ParrottSylowSeedData
