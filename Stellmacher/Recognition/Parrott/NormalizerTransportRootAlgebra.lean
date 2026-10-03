module

public import Stellmacher.Recognition.Parrott.NormalizerInvolutionTransportAlgebra

/-!
# The coordinate elimination in Parrott's transported root

Let L = ⟨u,t,z⟩. Once xˢ is in one of caL, cawL, cavL, cawvL and
fusion puts aˢ in u⟨v,z⟩, the supplied transport equations force aˢ ∈ u⟨z⟩
and xˢ ∈ cawL. The relation [x,a]=1 excludes the v-factor in aˢ.
Transporting the commutator with a excludes caL and cavL, and the square
identity excludes cawvL. These calculations preserve the literal transport.

The preliminary lemmas keep xˢ in K outside Ω₁(K), and give the explicit
conjugation y^(cu)=yaz for the separate fusion argument. The finite root
exhaustion and fusion assertions are premises here; their assembly belongs
to `NormalizerTransportRootCoordinates`.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.682, first paragraph. We use explicit words rather than the printed
centralizer equality: w does not centralize ca under equations (2) and (9).
-/

open Subgroup Tits
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

private theorem tail {p q o : G} (hp : p * q = o) (k : G) :
    p * (q * k) = o * k := by rw [← mul_assoc, hp]

private theorem comm_mul_left {p q r o : G}
    (hp : parrottCommutator p r = o) (hqr : Commute q r) (hqo : Commute q o) :
    parrottCommutator (p * q) r = o := by
  apply (parrottCommutator_eq_iff _ _ _).mpr
  have hp := (parrottCommutator_eq_iff _ _ _).mp hp
  calc
    p * q * r = p * r * q := by rw [mul_assoc, hqr.eq, ← mul_assoc]
    _ = r * p * o * q := by rw [hp]
    _ = r * (p * q) * o := by rw [mul_assoc (r*p), hqo.symm.eq]; simp only [mul_assoc]

private theorem comm_mul_right {p q r o : G}
    (hp : parrottCommutator p r = o) (hpq : Commute p q) (hqo : Commute q o) :
    parrottCommutator p (r * q) = o := by
  apply (parrottCommutator_eq_iff _ _ _).mpr
  have hp := (parrottCommutator_eq_iff _ _ _).mp hp
  calc
    p * (r * q) = r * p * o * q := by rw [← mul_assoc, hp]
    _ = r * p * q * o := by rw [mul_assoc (r*p), hqo.symm.eq, ← mul_assoc]
    _ = (r * q) * p * o := by rw [mul_assoc r p q, hpq.eq, ← mul_assoc]

private theorem small_centralizes (f : ParrottSylowGeneratorData n) {q : G}
    (hq : q ∈ closure ({f.u, n.t, z} : Set G)) :
    Commute q f.a ∧ Commute q f.u ∧ Commute q n.v ∧ Commute q n.t ∧ Commute q z := by
  have hle : closure ({f.u, n.t, z} : Set G) ≤ centralizer ({f.a, f.u, n.v, n.t, z} : Set G) := by
    apply (closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl <;>
      apply mem_centralizer_iff.mpr <;> intro r hr <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr <;>
      rcases hr with rfl | rfl | rfl | rfl | rfl
    all_goals first | exact (Commute.refl _).eq | exact f.comm_au.eq | exact f.comm_tu.symm.eq | exact f.comm_zu.symm.eq | exact f.comm_vu.eq | exact f.comm_at.eq | exact f.comm_tu.eq | exact f.comm_tv.symm.eq | exact f.comm_zt.symm.eq | exact f.comm_az.eq | exact f.comm_zu.eq | exact f.comm_zv.symm.eq | exact f.comm_zt.eq
  have hc := mem_centralizer_iff.mp (hle hq)
  exact ⟨(hc _ (by simp)).symm, (hc _ (by simp)).symm, (hc _ (by simp)).symm,
    (hc _ (by simp)).symm, (hc _ (by simp)).symm⟩

private theorem root_commutators (f : ParrottSylowGeneratorData n) {q : G}
    (hq : q ∈ closure ({f.u, n.t, z} : Set G)) :
    parrottCommutator (f.c * f.a * q) f.a = n.v * n.t ∧
    parrottCommutator (f.c * f.a * q) (f.u * n.v) = z ∧
    parrottCommutator (f.c * f.a * f.w * q) (f.u * n.v) = z ∧
    Commute (f.c * f.a * q) z ∧ Commute (f.c * f.a * f.w * q) z := by
  have hq := small_centralizes f hq
  have haa : f.a⁻¹ = f.a := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using f.a_sq)
  have hca : parrottCommutator (f.c * f.a) f.a = n.v * n.t := by
    calc
      _ = parrottCommutator f.a f.c := by
        simp only [parrottCommutator, mul_inv_rev, haa, mul_assoc]
        rw [← pow_two, f.a_sq, mul_one]
      _ = _ := f.eq12_ac
  have hcav : parrottCommutator (f.c * f.a) n.v = z :=
    comm_mul_left f.eq10_cv f.comm_av f.comm_az
  have hcauv : parrottCommutator (f.c * f.a) (f.u * n.v) = z := by
    rw [f.comm_vu.symm.eq]
    exact comm_mul_right hcav
      (((parrottCommutator_eq_one_iff _ _).mp f.eq09_cu).mul_left f.comm_au) f.comm_zu.symm
  have hcawuv : parrottCommutator (f.c * f.a * f.w) (f.u * n.v) = z :=
    comm_mul_left hcauv (f.comm_uw.symm.mul_right f.comm_vw.symm) f.comm_zw.symm
  exact ⟨comm_mul_left hca hq.1 (hq.2.2.1.mul_right hq.2.2.2.1),
    comm_mul_left hcauv (hq.2.1.mul_right hq.2.2.1) hq.2.2.2.2,
    comm_mul_left hcawuv (hq.2.1.mul_right hq.2.2.1) hq.2.2.2.2,
    (f.comm_zc.symm.mul_left f.comm_az).mul_left hq.2.2.2.2,
    ((f.comm_zc.symm.mul_left f.comm_az).mul_left f.comm_zw.symm).mul_left hq.2.2.2.2⟩

private theorem root_commutators_with_v (f : ParrottSylowGeneratorData n) {q : G}
    (hq : q ∈ closure ({f.u, n.t, z} : Set G)) :
    parrottCommutator (f.c * f.a * n.v * q) f.a = n.v * n.t ∧
    parrottCommutator (f.c * f.a * n.v * q) (f.u * n.v) = z ∧
    parrottCommutator (f.c * f.a * f.w * n.v * q) (f.u * n.v) = z ∧
    Commute (f.c * f.a * n.v * q) z ∧ Commute (f.c * f.a * f.w * n.v * q) z := by
  have hc := root_commutators f hq
  have hvq := (small_centralizes f hq).2.2.1.symm
  have he (p : G) : p * n.v * q = p * q * n.v := by
    rw [mul_assoc, hvq.eq, ← mul_assoc]
  rw [he, he]
  exact ⟨comm_mul_left hc.1 f.comm_av.symm ((Commute.refl n.v).mul_right f.comm_tv.symm),
    comm_mul_left hc.2.1 (f.comm_vu.mul_right (Commute.refl n.v)) f.comm_zv.symm,
    comm_mul_left hc.2.2.1 (f.comm_vu.mul_right (Commute.refl n.v)) f.comm_zv.symm,
    hc.2.2.2.1.mul_left f.comm_zv.symm, hc.2.2.2.2.mul_left f.comm_zv.symm⟩

private theorem cawv_tail_sq (f : ParrottSylowGeneratorData n) {q : G}
    (hq : q ∈ closure ({f.u, n.t, z} : Set G)) :
    (f.c * f.a * f.w * n.v * q) ^ 2 = (f.w * f.u * n.v * n.t * z) * z := by
  let p := f.c * f.a * f.w
  have hpv : parrottCommutator p n.v = z :=
    comm_mul_left (comm_mul_left f.eq10_cv f.comm_av f.comm_az)
      f.comm_vw.symm f.comm_zw.symm
  have hvp : n.v * p = p * n.v * z := by
    rw [(parrottCommutator_eq_iff _ _ _).mp hpv]
    simp only [mul_assoc, ← pow_two, f.z_sq, mul_one]
  have hvv : n.v * n.v = 1 := by simpa only [pow_two] using f.v_sq
  have hpv2 : (p * n.v) ^ 2 = p ^ 2 * z := by
    simp only [pow_two, mul_assoc, tail hvp, f.comm_zv.eq, tail hvv, one_mul]
  have hLF : closure ({f.u, n.t, z} : Set G) ≤ e.F := by
    rw [← f.elementary_basis]
    exact closure_mono (by intro g hg; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢; tauto)
  let _ := e.elementary
  have hq2 : q ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian q (hLF hq)
  have hLC : closure ({f.u, n.t, z} : Set G) ≤ centralizer ({p} : Set G) := by
    apply (closure_le _).mpr
    intro g hg
    apply mem_centralizer_singleton_iff.mpr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact ((((parrottCommutator_eq_one_iff _ _).mp f.eq09_cu).mul_left f.comm_au).mul_left f.comm_uw.symm).symm.eq
    · exact ((((parrottCommutator_eq_one_iff _ _).mp f.eq10_ct).mul_left f.comm_at).mul_left f.comm_tw.symm).symm.eq
    · exact ((f.comm_zc.symm.mul_left f.comm_az).mul_left f.comm_zw.symm).symm.eq
  have hpq : Commute p q := (mem_centralizer_singleton_iff.mp (hLC hq)).symm
  have hvq := (small_centralizes f hq).2.2.1.symm
  calc
    (p * n.v * q) ^ 2 = (p * n.v) ^ 2 * q ^ 2 := (hpq.mul_left hvq).mul_pow 2
    _ = p ^ 2 * z := by rw [hq2, mul_one, hpv2]
    _ = _ := by rw [show p ^ 2 = f.w * f.u * n.v * n.t * z from f.caw_sq]

/-- A concrete normalizer conjugator supplies the fusion input on p.682. -/
public theorem ParrottSylowGeneratorData.y_conj_cu (f : ParrottSylowGeneratorData n) :
    (f.c * f.u)⁻¹ * f.y * (f.c * f.u) = f.y * f.a * z := by
  have hyc : f.c⁻¹ * f.y * f.c = f.y * (f.a * n.t * z) := by
    calc
      _ = f.c⁻¹ * (f.y * f.c) := by group
      _ = _ := by rw [(parrottCommutator_eq_iff _ _ _).mp f.eq19_yc]; group
  have huy : f.u * f.y = f.y * f.u * n.t := by
    calc
      _ = f.y * ((MulAut.conj f.y⁻¹) f.u) := by
        simp only [MulAut.conj_apply, inv_inv]; group
      _ = _ := by rw [f.y_conjugation.2.1, mul_assoc]
  have hyu : f.y * f.u = f.u * f.y * n.t := by
    rw [huy]
    simp only [mul_assoc, ← pow_two, f.t_sq, mul_one]
  calc
    _ = f.u⁻¹ * (f.c⁻¹ * f.y * f.c) * f.u := by group
    _ = f.u⁻¹ * (f.y * (f.a * n.t * z)) * f.u := by rw [hyc]
    _ = f.u⁻¹ * (f.y * f.u) * (f.a * n.t * z) := by
      have hc : Commute f.u (f.a * n.t * z) :=
        (f.comm_au.symm.mul_right f.comm_tu.symm).mul_right f.comm_zu.symm
      rw [mul_assoc f.u⁻¹, mul_assoc f.y, hc.symm.eq]
      group
    _ = f.y * n.t * (f.a * n.t * z) := by rw [hyu]; group
    _ = _ := by
      have htt : n.t * n.t = 1 := by simpa only [pow_two] using f.t_sq
      simp only [mul_assoc, tail f.comm_at.symm.eq, tail htt, one_mul]

namespace ParrottNormalizerTransportData
variable {f : ParrottCentralizerGeneratorData n} (k : ParrottNormalizerTransportData f)

/-- The transported root remains in the literal normalizer core. -/
public theorem x_conj_mem_normalizer_core :
    k.s⁻¹ * f.x * k.s ∈ (pCore 2 (normalizer (e.F : Set G))).map
      (normalizer (e.F : Set G)).subtype := by
  let N := normalizer (e.F : Set G)
  let K := pCore 2 N
  have hN : N ≤ normalizer (K.map N.subtype : Set G) := by
    have hh := K.le_normalizer_map N.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  exact (mem_normalizer_iff''.mp (hN k.mem_normalizer) f.x).mp
    f.toParrottSylowGeneratorData.x_mem_normalizer_core

/-- Characteristicity of omega keeps the transported root outside it. -/
public theorem x_conj_not_mem_normalizer_omega :
    k.s⁻¹ * f.x * k.s ∉ (omega₁ (pCore 2 (normalizer (e.F : Set G))) (p := 2)).map
      ((normalizer (e.F : Set G)).subtype.comp (pCore 2 (normalizer (e.F : Set G))).subtype) := by
  let N := normalizer (e.F : Set G)
  let K := pCore 2 N
  let U := omega₁ K (p := 2)
  let V := U.map K.subtype
  let : U.Characteristic := omega₁_characteristic K
  let : V.Normal := ConjAct.normal_of_characteristic_of_normal
  have hN : N ≤ normalizer (V.map N.subtype : Set G) := by
    have hh := V.le_normalizer_map N.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  have hx : f.x ∉ V.map N.subtype := by
    simpa only [V, map_map] using f.toParrottSylowGeneratorData.x_not_mem_normalizer_omega
  intro hsx
  apply hx
  apply (mem_normalizer_iff''.mp (hN k.mem_normalizer) f.x).mpr
  simpa only [V, map_map] using hsx

private theorem comm_map (φ : MulAut G) (p q : G) :
    φ (parrottCommutator p q) = parrottCommutator (φ p) (φ q) := by
  simp only [parrottCommutator, map_mul, map_inv]

private theorem z_ne_one (n : ParrottNormalizerFusionData e) : z ≠ 1 := by
  intro hz
  obtain ⟨q, hq⟩ := n.three_conjugates_z_t
  have ht : n.t = 1 := by simpa [hz] using hq.symm
  have hh := n.t_order
  rw [ht, orderOf_one] at hh
  omega

/-- A root coordinate together with the four fusion alternatives rules out
both alternatives containing v, by transporting the relation [x,a]=1. -/
public theorem a_conj_of_root_coordinates
    (hx : ∃ q ∈ closure ({f.u, n.t, z} : Set G),
      k.s⁻¹ * f.x * k.s = f.c * f.a * q ∨
      k.s⁻¹ * f.x * k.s = f.c * f.a * f.w * q ∨
      k.s⁻¹ * f.x * k.s = f.c * f.a * n.v * q ∨
      k.s⁻¹ * f.x * k.s = f.c * f.a * f.w * n.v * q)
    (ha : k.s⁻¹ * f.a * k.s = f.u ∨ k.s⁻¹ * f.a * k.s = f.u * z ∨
      k.s⁻¹ * f.a * k.s = f.u * n.v ∨ k.s⁻¹ * f.a * k.s = f.u * n.v * z) :
    k.s⁻¹ * f.a * k.s = f.u ∨ k.s⁻¹ * f.a * k.s = f.u * z := by
  let S := MulAut.conj k.s⁻¹
  have hc : parrottCommutator (k.s⁻¹ * f.x * k.s) (k.s⁻¹ * f.a * k.s) = 1 := by
    have hh := congrArg S f.eq16_ax
    rw [comm_map, map_one] at hh
    simpa only [S, MulAut.conj_apply, inv_inv] using
      (parrottCommutator_eq_one_iff _ _).mpr
        ((parrottCommutator_eq_one_iff _ _).mp hh).symm
  obtain ⟨q, hq, hx⟩ := hx
  have hroot := root_commutators f.toParrottSylowGeneratorData hq
  have hrootv := root_commutators_with_v f.toParrottSylowGeneratorData hq
  have huv : parrottCommutator (k.s⁻¹ * f.x * k.s) (f.u * n.v) = z := by
    rcases hx with hx | hx | hx | hx
    · simpa only [hx] using hroot.2.1
    · simpa only [hx] using hroot.2.2.1
    · simpa only [hx] using hrootv.2.1
    · simpa only [hx] using hrootv.2.2.1
  have hcz : Commute (k.s⁻¹ * f.x * k.s) z := by
    rcases hx with hx | hx | hx | hx
    · simpa only [hx] using hroot.2.2.2.1
    · simpa only [hx] using hroot.2.2.2.2
    · simpa only [hx] using hrootv.2.2.2.1
    · simpa only [hx] using hrootv.2.2.2.2
  rcases ha with ha | ha | ha | ha
  · exact Or.inl ha
  · exact Or.inr ha
  · rw [ha, huv] at hc
    exact (z_ne_one (n := n) hc).elim
  · rw [ha, comm_mul_right huv hcz (Commute.refl z)] at hc
    exact (z_ne_one (n := n) hc).elim

/-- The commutator with a excludes both root branches without w, and the
square identity excludes the remaining v-factor. This assembles the first
paragraph of p.682 from root exhaustion and elementary fusion. -/
public theorem root_coordinates_of_exhaustion_and_fusion
    (hx : ∃ q ∈ closure ({f.u, n.t, z} : Set G),
      k.s⁻¹ * f.x * k.s = f.c * f.a * q ∨
      k.s⁻¹ * f.x * k.s = f.c * f.a * f.w * q ∨
      k.s⁻¹ * f.x * k.s = f.c * f.a * n.v * q ∨
      k.s⁻¹ * f.x * k.s = f.c * f.a * f.w * n.v * q)
    (ha : k.s⁻¹ * f.a * k.s = f.u ∨ k.s⁻¹ * f.a * k.s = f.u * z ∨
      k.s⁻¹ * f.a * k.s = f.u * n.v ∨ k.s⁻¹ * f.a * k.s = f.u * n.v * z) :
    (k.s⁻¹ * f.a * k.s = f.u ∨ k.s⁻¹ * f.a * k.s = f.u * z) ∧
    (f.c * f.a * f.w)⁻¹ * (k.s⁻¹ * f.x * k.s) ∈ closure ({f.u, n.t, z} : Set G) := by
  have ha := k.a_conj_of_root_coordinates hx ha
  refine ⟨ha, ?_⟩
  have hxa : parrottCommutator f.x (k.s⁻¹ * f.a * k.s) = n.v := by
    rcases ha with ha | ha
    · rw [ha]; exact f.eq01_xu
    · rw [ha]; exact comm_mul_right f.eq01_xu f.comm_zx.symm f.comm_zv
  let S := MulAut.conj k.s⁻¹
  have hss : ∀ g : G, S (S g) = g := by
    intro g
    have hi : k.s⁻¹ = k.s := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using k.sq)
    change k.s⁻¹ * (k.s⁻¹ * g * k.s⁻¹⁻¹) * k.s⁻¹⁻¹ = g
    simp only [hi]
    have hsq : k.s * k.s = 1 := by simpa only [pow_two] using k.sq
    simp only [← mul_assoc, hsq, one_mul]
    rw [mul_assoc, hsq, mul_one]
  have hmap := congrArg S hxa
  have hSa : k.s⁻¹ * f.a * k.s = S f.a := by simp only [S, MulAut.conj_apply, inv_inv]
  rw [hSa] at hmap
  rw [comm_map, hss] at hmap
  simp only [S, MulAut.conj_apply, inv_inv] at hmap
  rw [k.v_conj] at hmap
  obtain ⟨q, hq, hx | hx | hx | hx⟩ := hx
  · have hc := (root_commutators f.toParrottSylowGeneratorData hq).1
    rw [hx, hc] at hmap
    have hz : z = 1 := mul_left_cancel (hmap.symm.trans (mul_one (n.v * n.t)).symm)
    exact (z_ne_one (n := n) hz).elim
  · rw [hx]
    simpa only [inv_mul_cancel_left] using hq
  · have hc := (root_commutators_with_v f.toParrottSylowGeneratorData hq).1
    rw [hx, hc] at hmap
    have hz : z = 1 := mul_left_cancel (hmap.symm.trans (mul_one (n.v * n.t)).symm)
    exact (z_ne_one (n := n) hz).elim
  · have hc := cawv_tail_sq f.toParrottSylowGeneratorData hq
    have hs := k.x_conj_sq
    rw [hx, hc] at hs
    have hz : z = 1 := mul_left_cancel (hs.trans (mul_one _).symm)
    exact (z_ne_one (n := n) hz).elim

end ParrottNormalizerTransportData
end Stellmacher.Recognition
