module

public import Stellmacher.Recognition.Parrott.CentralizerInvolutionSeed

/-!
# The elementary action determined by Parrott's core action

Put H = C_G(z), J = O₂(H), and E = J′, with subgroups interpreted through
their actual inclusions in G. An element r of H whose core images modulo E
are a ↦ d, b ↦ dcb and d ↦ a necessarily sends t to wuv and v to uv modulo
⟨z⟩. This is conditional on the supplied action; no involution is constructed.

The proof works in J/Z(J). Since J′ = Z₂(J), the errors in the core images
become central and disappear from commutators. The normalized equations give
[a,b] = t and [d,b] = v, while [d,dcb] = wuv and [a,dcb] = uv modulo Z(J).
Conjugation preserves commutators. Finally the actual ambient image of Z(J)
is ⟨z⟩ by Parrott's centralizer structure theorem. This argument needs only
three of the four prescribed images and does not need r² = 1; the final
wrapper retains all hypotheses of the geometric selection interface.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed pp.680–681 through equation (21).
-/

open Subgroup

namespace Stellmacher.Recognition

private theorem pc_mul_right {Q : Type*} [Group Q] (a b c : Q)
    (h : Commute (Tits.parrottCommutator a b) c) :
    Tits.parrottCommutator a (b*c) =
      Tits.parrottCommutator a c * Tits.parrottCommutator a b := by
  calc
    _ = Tits.parrottCommutator a c * (c⁻¹ * Tits.parrottCommutator a b * c) := by
      simp only [Tits.parrottCommutator]; group
    _ = _ := by rw [mul_assoc c⁻¹, h.eq, inv_mul_cancel_left]

private theorem pc_central_right {Q : Type*} [Group Q] (a b c : Q)
    (hc : c ∈ center Q) :
    Tits.parrottCommutator a (b*c) = Tits.parrottCommutator a b := by
  rw [pc_mul_right a b c (mem_center_iff.mp hc _),
    (Tits.parrottCommutator_eq_one_iff a c).mpr (mem_center_iff.mp hc a), one_mul]

private theorem pc_swap {Q : Type*} [Group Q] (a b : Q) :
    Tits.parrottCommutator a b = (Tits.parrottCommutator b a)⁻¹ := by
  simp only [Tits.parrottCommutator]; group

private theorem pc_central_left {Q : Type*} [Group Q] (a b c : Q)
    (hc : c ∈ center Q) :
    Tits.parrottCommutator (a*c) b = Tits.parrottCommutator a b := by
  rw [pc_swap, pc_central_right b a c hc, ← pc_swap]

private theorem pc_perturb {Q : Type*} [Group Q] (a b a' b' : Q)
    (ha : a⁻¹*a' ∈ center Q) (hb : b⁻¹*b' ∈ center Q) :
    Tits.parrottCommutator a' b' = Tits.parrottCommutator a b := by
  calc
    _ = Tits.parrottCommutator (a*(a⁻¹*a')) (b*(b⁻¹*b')) := by simp
    _ = _ := by rw [pc_central_left _ _ _ ha, pc_central_right _ _ _ hb]

private theorem pc_self {Q : Type*} [Group Q] (a : Q) :
    Tits.parrottCommutator a a = 1 := by simp [Tits.parrottCommutator]

private theorem pc_map {Q R : Type*} [Group Q] [Group R] (q : Q →* R) (a b : Q) :
    q (Tits.parrottCommutator a b) = Tits.parrottCommutator (q a) (q b) := by
  simp only [Tits.parrottCommutator, map_mul, map_inv]

private theorem word_transfer {Q : Type*} [Group Q] (a b c d t v u w : Q)
    (ht : t ∈ center Q) (hv : v ∈ center Q) (hu : u ∈ center Q) (hw : w ∈ center Q)
    (htt : t ^ 2 = 1) (huu : u ^ 2 = 1) (hww : w ^ 2 = 1)
    (hdb : Tits.parrottCommutator d b = v)
    (hab : Tits.parrottCommutator a b = t)
    (hac : Tits.parrottCommutator a c = v*t)
    (had : Tits.parrottCommutator a d = u)
    (hcd : Tits.parrottCommutator c d = w*u) :
    Tits.parrottCommutator d (d*c*b) = w*u*v ∧
    Tits.parrottCommutator a (d*c*b) = u*v := by
  have hdc : Tits.parrottCommutator d c = w*u := by
    have hwu : (w*u)^2 = 1 := by
      rw [(show Commute w u from (mem_center_iff.mp hw u).symm).mul_pow, hww, huu, one_mul]
    rw [pc_swap, hcd]
    exact inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hwu)
  constructor
  · rw [pc_mul_right d (d*c) b, pc_mul_right d d c, pc_self, mul_one, hdc, hdb]
    · exact mem_center_iff.mp (mul_mem hw hu) v
    · rw [pc_self]; exact Commute.one_left c
    · rw [pc_mul_right d d c (by rw [pc_self]; exact Commute.one_left c), pc_self,
        mul_one, hdc]
      exact (mem_center_iff.mp (mul_mem hw hu) b).symm
  · rw [pc_mul_right a (d*c) b, pc_mul_right a d c, had, hac, hab]
    · calc
        t * (v*t*u) = t * (t*v*u) := by rw [mem_center_iff.mp ht v]
        _ = (t*t)*(v*u) := by simp only [mul_assoc]
        _ = (t*t)*(u*v) := by rw [mem_center_iff.mp hu v]
        _ = u*v := by rw [← pow_two, htt, one_mul]
    · rw [had]; exact (mem_center_iff.mp hu c).symm
    · rw [pc_mul_right a d c (by rw [had]; exact (mem_center_iff.mp hu c).symm), hac, had]
      exact (mem_center_iff.mp (mul_mem (mul_mem hv ht) hu) b).symm

private theorem intrinsic_transfer {K : Type*} [Group K]
    (hupper : commutator K = Subgroup.upperCentralSeries K 2)
    (R : K ≃* K) (a b c d t v u w : K)
    (ht : t ∈ commutator K) (hv : v ∈ commutator K)
    (hu : u ∈ commutator K) (hw : w ∈ commutator K)
    (htt : t ^ 2 = 1) (huu : u ^ 2 = 1) (hww : w ^ 2 = 1)
    (hdb : Tits.parrottCommutator d b = v)
    (hab : Tits.parrottCommutator a b = t)
    (hac : Tits.parrottCommutator a c = v*t)
    (had : Tits.parrottCommutator a d = u)
    (hcd : Tits.parrottCommutator c d = w*u)
    (hra : d⁻¹ * R a ∈ commutator K)
    (hrb : (d*c*b)⁻¹ * R b ∈ commutator K)
    (hrd : a⁻¹ * R d ∈ commutator K) :
    (w*u*v)⁻¹ * R t ∈ center K ∧ (u*v)⁻¹ * R v ∈ center K := by
  let Q := K ⧸ center K
  let q := QuotientGroup.mk' (center K)
  have hD : commutator K ≤ (center Q).comap q := by
    rw [hupper, ← Subgroup.comap_upperCentralSeries_quotient_center 1,
      Subgroup.upperCentralSeries_one]
  have hh := word_transfer (q a) (q b) (q c) (q d) (q t) (q v) (q u) (q w)
    (hD ht) (hD hv) (hD hu) (hD hw)
    (by rw [← map_pow, htt, map_one])
    (by rw [← map_pow, huu, map_one])
    (by rw [← map_pow, hww, map_one])
    (by rw [← pc_map, hdb])
    (by rw [← pc_map, hab])
    (by rw [← pc_map, hac, map_mul])
    (by rw [← pc_map, had])
    (by rw [← pc_map, hcd, map_mul])
  have ha' : (q d)⁻¹ * q (R a) ∈ center Q := by
    simpa only [mem_comap, map_mul, map_inv] using hD hra
  have hb' : (q (d*c*b))⁻¹ * q (R b) ∈ center Q := by
    simpa only [mem_comap, map_mul, map_inv] using hD hrb
  have hd' : (q a)⁻¹ * q (R d) ∈ center Q := by
    simpa only [mem_comap, map_mul, map_inv] using hD hrd
  have hqt : q (R t) = q (w*u*v) := by
    calc
      _ = Tits.parrottCommutator (q (R a)) (q (R b)) := by
        rw [← hab]; simp only [Tits.parrottCommutator, map_mul, map_inv]
      _ = Tits.parrottCommutator (q d) (q (d*c*b)) := pc_perturb _ _ _ _ ha' hb'
      _ = _ := by simpa only [map_mul] using hh.1
  have hqv : q (R v) = q (u*v) := by
    calc
      _ = Tits.parrottCommutator (q (R d)) (q (R b)) := by
        rw [← hdb]; simp only [Tits.parrottCommutator, map_mul, map_inv]
      _ = Tits.parrottCommutator (q a) (q (d*c*b)) := pc_perturb _ _ _ _ hd' hb'
      _ = _ := by simpa only [map_mul] using hh.2
  exact ⟨QuotientGroup.eq.mp hqt.symm, QuotientGroup.eq.mp hqv.symm⟩

variable {G : Type*} [Group G] {z : G} {e : ParrottSecondElementaryData z}
  {n : ParrottNormalizerFusionData e}

/-- The images of a, b and d modulo the derived core already determine the
images of t and v modulo the center. No involutivity assumption is needed. -/
public theorem ParrottSylowGeneratorData.t_v_conj_mod_center_of_three_core_images [Finite G]
    (f : ParrottSylowGeneratorData n) (h : ParrottCentralizerHypotheses z)
    (r : G) (hrH : r ∈ centralizer ({z} : Set G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    f.d⁻¹ * (r⁻¹ * f.a * r) ∈ E →
    (f.d * f.c * f.b)⁻¹ * (r⁻¹ * f.b * r) ∈ E →
    f.a⁻¹ * (r⁻¹ * f.d * r) ∈ E →
    (f.w * f.u * n.v)⁻¹ * (r⁻¹ * n.t * r) ∈ zpowers z ∧
      (f.u * n.v)⁻¹ * (r⁻¹ * n.v * r) ∈ zpowers z := by
  dsimp only
  intro hra hrb hrd
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let ι : J →* G := H.subtype.comp J.subtype
  have hι : Function.Injective ι := H.subtype_injective.comp J.subtype_injective
  have hgen (g : G) (hg : g ∈ ({f.a, f.b, f.c, f.d} : Set G)) :
      ∃ j : J, ι j = g := by
    have hm : g ∈ J.map H.subtype := f.core_generators ▸ subset_closure hg
    obtain ⟨gH, hgJ, hgg⟩ := hm
    exact ⟨⟨gH, hgJ⟩, hgg⟩
  obtain ⟨a, ha⟩ := hgen f.a (by simp)
  obtain ⟨b, hb⟩ := hgen f.b (by simp)
  obtain ⟨c, hc⟩ := hgen f.c (by simp)
  obtain ⟨d, hd⟩ := hgen f.d (by simp)
  have hder (g : G) (hg : g ∈ ({z, n.t, n.v, f.u, f.w} : Set G)) :
      ∃ j : J, j ∈ commutator J ∧ ι j = g := by
    change g ∈ (commutator J).map ι
    rw [← f.derived_basis]
    exact subset_closure hg
  obtain ⟨t, htD, ht⟩ := hder n.t (by simp)
  obtain ⟨v, hvD, hv⟩ := hder n.v (by simp)
  obtain ⟨u, huD, hu⟩ := hder f.u (by simp)
  obtain ⟨w, hwD, hw⟩ := hder f.w (by simp)
  let rH : H := ⟨r, hrH⟩
  let R : J ≃* J := MulAut.conjNormal rH⁻¹
  have hR (j : J) : ι (R j) = r⁻¹ * ι j * r := by
    change r⁻¹ * ι j * (r⁻¹)⁻¹ = r⁻¹ * ι j * r
    rw [inv_inv]
  have hDlift (j : J) (hj : ι j ∈ (commutator J).map ι) : j ∈ commutator J := by
    obtain ⟨k, hk, hkj⟩ := hj
    exact hι hkj ▸ hk
  obtain ⟨hZ, _, _, _, hupper, _, _, _⟩ := parrott_centralizer_structure z h
  have hh := intrinsic_transfer hupper R a b c d t v u w htD hvD huD hwD
    (hι (by simpa only [map_pow, map_one, ht] using f.t_sq))
    (hι (by simpa only [map_pow, map_one, hu] using f.u_sq))
    (hι (by simpa only [map_pow, map_one, hw] using f.w_sq))
    (hι (by simpa only [pc_map, hd, hb, hv] using f.eq03_db))
    (hι (by simpa only [pc_map, ha, hb, ht] using f.eq05_ab))
    (hι (by simpa only [pc_map, map_mul, ha, hc, hv, ht] using f.eq12_ac))
    (hι (by simpa only [pc_map, ha, hd, hu] using f.eq11_ad))
    (hι (by simpa only [pc_map, map_mul, hc, hd, hw, hu] using f.eq14_cd))
    (hDlift _ (by simpa only [map_mul, map_inv, hR, hd, ha] using hra))
    (hDlift _ (by simpa only [map_mul, map_inv, hR, hd, hc, hb] using hrb))
    (hDlift _ (by simpa only [map_mul, map_inv, hR, ha, hd] using hrd))
  change (center J).map ι = zpowers z at hZ
  constructor
  · rw [← hZ]
    exact ⟨_, hh.1, by simp only [map_mul, map_inv, hR, hw, hu, hv, ht]⟩
  · rw [← hZ]
    exact ⟨_, hh.2, by simp only [map_mul, map_inv, hR, hu, hv]⟩

/-- Transfer an oriented involution action on J/E to equations (20)–(21)
on E/⟨z⟩. The fourth core image and involutivity are retained in this
interface for the geometric selection theorem. -/
public theorem ParrottSylowGeneratorData.t_v_conj_mod_center_of_core_action [Finite G]
    (f : ParrottSylowGeneratorData n) (h : ParrottCentralizerHypotheses z)
    (r : G) (hrH : r ∈ centralizer ({z} : Set G)) (_hr2 : r ^ 2 = 1) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    f.d⁻¹ * (r⁻¹ * f.a * r) ∈ E →
    (f.d * f.c * f.b)⁻¹ * (r⁻¹ * f.b * r) ∈ E →
    (f.c * f.d * f.a)⁻¹ * (r⁻¹ * f.c * r) ∈ E →
    f.a⁻¹ * (r⁻¹ * f.d * r) ∈ E →
    (f.w * f.u * n.v)⁻¹ * (r⁻¹ * n.t * r) ∈ zpowers z ∧
      (f.u * n.v)⁻¹ * (r⁻¹ * n.v * r) ∈ zpowers z := by
  dsimp only
  intro hra hrb _hrc hrd
  exact f.t_v_conj_mod_center_of_three_core_images h r hrH hra hrb hrd

end Stellmacher.Recognition
