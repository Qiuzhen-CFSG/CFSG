module

public import Stellmacher.Recognition.Parrott.SylowCoreCovarianceData

/-!
# Covariance of Parrott's initial core commutators

For the supplied initial frame, put P(g) = x⁻¹gx, p = [a,d], q = [a,c],
r = [b,c], and k = c². We prove the four identities of `CoreCovariance`
without choosing the later core cosets or changing any coordinate.

The calculation takes place in J / Z(J). The derived subgroup is elementary
and equals Z₂(J), so derived errors become central involutions. The outer
images a, ba, cab, dabc give P(p) = ptq and P(q) = qt. Transporting
[d,b] = v and P(v) = vt gives pqr = t. Thus q = P(p)pt, r = P(p),
and P²(p) = pt. Finally P(k) = (cab)² = kvtqr = kvp.
The elementary second-center square lemma removes the error in P(c).
The actual inclusion J → C_G(z) → G sends Z(J) onto ⟨z⟩, giving the
four required ambient memberships.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed pp.678–679, the calculations after equations (1)–(10).
-/

set_option linter.unusedSimpArgs false
open Subgroup
namespace Stellmacher.Recognition.ParrottSylowInitialData
private theorem pc_map {Q R : Type*} [Group Q] [Group R] (q : Q →* R) (a b : Q) :
    q (Tits.parrottCommutator a b) = Tits.parrottCommutator (q a) (q b) := by
  simp only [Tits.parrottCommutator, map_mul, map_inv]
private theorem pc_swap {Q : Type*} [Group Q] (a b : Q) :
    Tits.parrottCommutator a b = (Tits.parrottCommutator b a)⁻¹ := by
  simp only [Tits.parrottCommutator]; group
private theorem pc_mul_right {Q : Type*} [Group Q] (a b c : Q)
    (h : Commute (Tits.parrottCommutator a b) c) :
    Tits.parrottCommutator a (b * c) =
      Tits.parrottCommutator a c * Tits.parrottCommutator a b := by
  calc
    _ = Tits.parrottCommutator a c * (c⁻¹ * Tits.parrottCommutator a b * c) := by
      simp only [Tits.parrottCommutator]; group
    _ = _ := by rw [mul_assoc c⁻¹, h.eq, inv_mul_cancel_left]
private theorem pc_central_right {Q : Type*} [Group Q] (a b c : Q)
    (hc : c ∈ center Q) :
    Tits.parrottCommutator a (b * c) = Tits.parrottCommutator a b := by
  rw [pc_mul_right a b c (mem_center_iff.mp hc _),
    (Tits.parrottCommutator_eq_one_iff a c).mpr (mem_center_iff.mp hc a), one_mul]
private theorem pc_perturb {Q : Type*} [Group Q] (a b a' b' : Q)
    (ha : a' / a ∈ center Q) (hb : b' / b ∈ center Q) :
    Tits.parrottCommutator a' b' = Tits.parrottCommutator a b := by
  have hr (x y : Q) (hy : y / x ∈ center Q) :
      ∀ w, Tits.parrottCommutator w y = Tits.parrottCommutator w x := by
    intro w
    have he : y = x * (y / x) := by
      rw [(mem_center_iff.mp hy x)]; simp
    rw [he, pc_central_right _ _ _ hy]
  rw [hr b b' hb, pc_swap, hr a a' ha, ← pc_swap]

private theorem word_covariance {Q : Type*} [Group Q]
    (hcentral : ∀ a b : Q, Tits.parrottCommutator a b ∈ center Q)
    (hexp : ∀ a b : Q, Tits.parrottCommutator a b ^ 2 = 1)
    (P : Q ≃* Q) (a b c d t v : Q)
    (hab : Tits.parrottCommutator a b = t)
    (hdb : Tits.parrottCommutator d b = v)
    (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = v)
    (hPt : P t = t) (hPv : P v = v * t)
    (ha : P a / a ∈ center Q) (hb : P b / (b * a) ∈ center Q)
    (hc : P c / (c * a * b) ∈ center Q) (hd : P d / (d * a * b * c) ∈ center Q)
    (hcs : (P c) ^ 2 = (c * a * b) ^ 2) :
    Tits.parrottCommutator a c = P (Tits.parrottCommutator a d) *
      Tits.parrottCommutator a d * t ∧
    Tits.parrottCommutator b c = P (Tits.parrottCommutator a d) ∧
    P (P (Tits.parrottCommutator a d)) = Tits.parrottCommutator a d * t ∧
    P (c ^ 2) = c ^ 2 * v * Tits.parrottCommutator a d := by
  -- All subsequent coefficient calculations live in the commutative center.
  let C (g k : Q) : center Q := ⟨Tits.parrottCommutator g k, hcentral g k⟩
  have Csq (g k : Q) : C g k * C g k = 1 :=
    Subtype.ext (by simpa only [C, Subgroup.coe_mul, Subgroup.coe_one, pow_two] using hexp g k)
  have Cinv (g k : Q) : (C g k)⁻¹ = C g k := inv_eq_of_mul_eq_one_right (Csq g k)
  have Cswap (g k : Q) : C g k = C k g := by
    apply Subtype.ext
    change Tits.parrottCommutator g k = Tits.parrottCommutator k g
    rw [pc_swap]
    exact congrArg Subtype.val (Cinv k g)
  have Cself (g : Q) : C g g = 1 := by apply Subtype.ext; simp [C, Tits.parrottCommutator]
  have Cright (g j k : Q) : C g (j * k) = C g j * C g k := by
    apply Subtype.ext
    exact (pc_mul_right g j k (mem_center_iff.mp (hcentral g j) k).symm).trans
      (mem_center_iff.mp (hcentral g j) _)
  have Cleft (g j k : Q) : C (g * j) k = C g k * C j k := by
    rw [Cswap, Cright, Cswap k g, Cswap k j]
  let R : center Q ≃* center Q := MulAut.characteristic (center Q) P
  have RC (g k : Q) : R (C g k) = C (P g) (P k) :=
    Subtype.ext (pc_map P.toMonoidHom g k)
  have perturb (g k g' k' : Q) (hg : g'/g ∈ center Q) (hk : k'/k ∈ center Q) :
      C g' k'=C g k := Subtype.ext (pc_perturb g k g' k' hg hk)
  have Rt : R (C a b) = C a b := by
    apply Subtype.ext
    change P (Tits.parrottCommutator a b) = Tits.parrottCommutator a b
    rw [hab, hPt]
  have Rv : R (C d b) = C d b * C a b :=
    Subtype.ext (by
      change P (Tits.parrottCommutator d b) =
        Tits.parrottCommutator d b * Tits.parrottCommutator a b
      rw [hdb, hab, hPv])
  have Rp : R (C a d) = C a d * C a b * C a c := by
    rw [RC, perturb _ _ _ _ ha hd]
    simp only [Cright, Cself, mul_one]
  have Rq : R (C a c) = C a c * C a b := by
    rw [RC, perturb _ _ _ _ ha hc]
    simp only [Cright, Cself, mul_one]
  -- Transport [d,b] = v; cancellation of v gives pqr = t.
  have relation : C a d * C a c * C b c = C a b := by
    have hh := Rv
    rw [RC, perturb _ _ _ _ hd hb] at hh
    simp only [Cleft, Cright, Cself, one_mul, mul_one] at hh
    rw [Cswap b a, Cswap c b, Cswap c a, Cswap d a] at hh
    have he : C d b * (C a d * C a c * C b c) = C d b * C a b := by
      calc
        _ = (C d b * C a d * C a b * (C a b * C b c * C a c)) := by
          rw [show C d b * C a d * C a b * (C a b * C b c * C a c) =
            C d b * (C a d * C a c * C b c) * (C a b * C a b) by ac_rfl, Csq, mul_one]
        _ = _ := by simpa only [mul_assoc] using hh
    exact mul_left_cancel he
  have qeq : C a c = R (C a d) * C a d * C a b := by
    rw [Rp]
    symm
    calc
      _ = C a c * (C a d * C a d) * (C a b * C a b) := by ac_rfl
      _ = _ := by rw [Csq, Csq, mul_one, mul_one]
  have req : C b c = R (C a d) := by
    rw [Rp]
    have he := congrArg (fun s => s * C a d * C a c) relation
    have he' : C b c = C a b * C a d * C a c := by
      convert he using 1
      · symm
        calc
          _ = C b c * (C a d * C a d) * (C a c * C a c) := by ac_rfl
          _ = _ := by rw [Csq, Csq, mul_one, mul_one]
    exact he'.trans (by ac_rfl)
  have ppeq : R (R (C a d)) = C a d * C a b := by
    rw [Rp, map_mul, map_mul, Rp, Rt, Rq]
    calc
      _ = (C a d * C a b) * (C a b * C a b) * (C a c * C a c) := by ac_rfl
      _ = _ := by rw [Csq, Csq, mul_one, mul_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hh := congrArg Subtype.val qeq
    change Tits.parrottCommutator a c = P (Tits.parrottCommutator a d) *
      Tits.parrottCommutator a d * Tits.parrottCommutator a b at hh
    simpa only [hab] using hh
  · exact congrArg Subtype.val req
  · have hh := congrArg Subtype.val ppeq
    change P (P (Tits.parrottCommutator a d)) =
      Tits.parrottCommutator a d * Tits.parrottCommutator a b at hh
    simpa only [hab] using hh
  · have sq (g k : Q) : (g * k) ^ 2 = g ^ 2 * k ^ 2 * Tits.parrottCommutator k g := by
      have hc := (mem_center_iff.mp (hcentral k g) k)
      calc
        _ = g * g * k * Tits.parrottCommutator k g * k := by
          simp only [Tits.parrottCommutator, pow_two]; group
        _ = _ := by rw [mul_assoc (g * g * k), ← hc]; simp only [pow_two, mul_assoc]
    rw [map_pow, hcs, sq, sq, ha2, mul_one, hb2]
    have hcba : Tits.parrottCommutator b (c * a) =
        Tits.parrottCommutator b c * Tits.parrottCommutator a b := by
      exact congrArg Subtype.val (by rw [Cright, Cswap b a] : C b (c * a) = C b c * C a b)
    rw [hcba]
    have he : Tits.parrottCommutator a c *
        Tits.parrottCommutator b c * t = Tits.parrottCommutator a d := by
      have hh : C a c * C b c * C a b = C a d := by
        rw [req, Rp]
        calc
          _ = C a d * (C a c * C a c) * (C a b * C a b) := by ac_rfl
          _ = _ := by rw [Csq, Csq, mul_one, mul_one]
      simpa only [C, Subgroup.coe_mul, hab] using congrArg Subtype.val hh
    rw [← hab] at he
    calc
      _ = c ^ 2 * v * (Tits.parrottCommutator a c * Tits.parrottCommutator b c *
        Tits.parrottCommutator a b) := by
        rw [mul_assoc (c ^ 2), (mem_center_iff.mp (hcentral a c) v).symm]
        simp only [mul_assoc]
      _ = _ := by rw [he]

private theorem intrinsic_covariance {K : Type*} [Group K]
    [IsElementaryAbelian 2 (commutator K)]
    (hupper : commutator K = Subgroup.upperCentralSeries K 2)
    (R : K ≃* K) (a b c d t v : K)
    (hab : Tits.parrottCommutator a b = t)
    (hdb : Tits.parrottCommutator d b = v)
    (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = v)
    (hRt : R t = t) (hRv : R v = v * t)
    (ha : R a / a ∈ commutator K)
    (hb : R b / (b * a) ∈ commutator K)
    (hc : R c / (c * a * b) ∈ commutator K)
    (hd : R d / (d * a * b * c) ∈ commutator K) :
    Tits.parrottCommutator a c / (R (Tits.parrottCommutator a d) *
      Tits.parrottCommutator a d * t) ∈ center K ∧
    Tits.parrottCommutator b c / R (Tits.parrottCommutator a d) ∈ center K ∧
    R (R (Tits.parrottCommutator a d)) / (Tits.parrottCommutator a d * t) ∈ center K ∧
    R (c ^ 2) / (c ^ 2 * v * Tits.parrottCommutator a d) ∈ center K := by
  let Q := K ⧸ center K
  let q := QuotientGroup.mk' (center K)
  let P : Q ≃* Q := QuotientGroup.congr (center K) (center K) R
    (characteristic_iff_map_eq.mp inferInstance R)
  have hP (g : K) : P (q g) = q (R g) := rfl
  have hD : commutator K ≤ (center Q).comap q := by
    rw [hupper, ← Subgroup.comap_upperCentralSeries_quotient_center 1,
      Subgroup.upperCentralSeries_one]
  have hpc (g k : K) : Tits.parrottCommutator g k ∈ commutator K := by
    simpa only [Tits.parrottCommutator, _root_.commutator_def, commutatorElement_def, inv_inv] using
      commutator_mem_commutator (H₁ := (⊤ : Subgroup K)) (H₂ := ⊤)
        (g₁ := g⁻¹) (g₂ := k⁻¹) (mem_top _) (mem_top _)
  have hcentral (g k : Q) : Tits.parrottCommutator g k ∈ center Q := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (center K) g
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (center K) k
    simpa only [mem_comap, pc_map] using hD (hpc g k)
  have hexp (g k : Q) : Tits.parrottCommutator g k ^ 2 = 1 := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (center K) g
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (center K) k
    have hs := elemPow_eq_one_of_isElementaryAbelian (p := 2) _ (hpc g k)
    simpa only [map_pow, map_one, pc_map] using congrArg q hs
  -- A derived error does not affect the square modulo the center.
  have hcs : (P (q c)) ^ 2 = (q c * q a * q b) ^ 2 := by
    have hs := sq_eq_mod_center_of_eq_mod_elementary (commutator K) hupper.le
      (R c) (c * a * b) (QuotientGroup.eq_iff_div_mem.mpr hc)
    simpa only [hP, map_pow, map_mul] using hs
  have hh := word_covariance hcentral hexp P (q a) (q b) (q c) (q d) (q t) (q v)
    (by rw [← pc_map, hab]) (by rw [← pc_map, hdb])
    (by rw [← map_pow, ha2, map_one]) (by rw [← map_pow, hb2])
    (by rw [hP, hRt]) (by rw [hP, hRv, map_mul])
    (by simpa only [mem_comap, map_div, hP] using hD ha)
    (by simpa only [mem_comap, map_div, map_mul, hP] using hD hb)
    (by simpa only [mem_comap, map_div, map_mul, hP] using hD hc)
    (by simpa only [mem_comap, map_div, map_mul, hP] using hD hd) hcs
  have h1 : q (Tits.parrottCommutator a c) =
      q (R (Tits.parrottCommutator a d) * Tits.parrottCommutator a d * t) := by
    simpa only [map_mul, ← pc_map, hP] using hh.1
  have h2 : q (Tits.parrottCommutator b c) = q (R (Tits.parrottCommutator a d)) := by
    simpa only [← pc_map, hP] using hh.2.1
  have h3 : q (R (R (Tits.parrottCommutator a d))) =
      q (Tits.parrottCommutator a d * t) := by
    simpa only [map_mul, ← pc_map, hP] using hh.2.2.1
  have h4 : q (R (c ^ 2)) = q (c ^ 2 * v * Tits.parrottCommutator a d) := by
    simpa only [map_mul, ← map_pow, ← pc_map, hP] using hh.2.2.2
  exact ⟨QuotientGroup.eq_iff_div_mem.mp h1, QuotientGroup.eq_iff_div_mem.mp h2,
    QuotientGroup.eq_iff_div_mem.mp h3, QuotientGroup.eq_iff_div_mem.mp h4⟩

variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

/-- The four covariance identities of the initial core frame, with every
supplied coordinate retained. -/
public theorem core_covariance [Finite G] (f : ParrottSylowInitialData n)
    (h : ParrottCentralizerHypotheses z) : f.CoreCovariance := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let ι : J →* G := H.subtype.comp J.subtype
  have hι : Function.Injective ι := H.subtype_injective.comp J.subtype_injective
  have hgen (g : G) (hg : g ∈ ({f.a,f.b,f.c,f.d} : Set G)) :
      ∃ j : J, ι j = g := by
    obtain ⟨gH, hgJ, hgg⟩ := f.generators_mem_core g hg
    exact ⟨⟨gH, hgJ⟩, hgg⟩
  obtain ⟨a, ha⟩ := hgen f.a (by simp)
  obtain ⟨b, hb⟩ := hgen f.b (by simp)
  obtain ⟨c, hc⟩ := hgen f.c (by simp)
  obtain ⟨d, hd⟩ := hgen f.d (by simp)
  obtain ⟨t, _, ht⟩ := f.basis_mem_derived n.t (by simp)
  obtain ⟨v, _, hv⟩ := f.basis_mem_derived n.v (by simp)
  change ι t = n.t at ht
  change ι v = n.v at hv
  have hxH : f.x ∈ H := e.sylow_le_centralizer
    (f.sylow_eq.symm ▸ mem_sup_left (mem_zpowers f.x))
  let xH : H := ⟨f.x, hxH⟩
  let R : J ≃* J := MulAut.conjNormal xH⁻¹
  let A : G ≃* G := MulAut.conj f.x⁻¹
  have hR (j : J) : ι (R j) = A (ι j) := rfl
  have hA (g : G) : A g = f.x⁻¹ * g * f.x := by simp [A]
  have hAt : A n.t = n.t := by
    rw [hA, mul_assoc, ((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq01_xt).symm.eq,
      inv_mul_cancel_left]
  have hAv : A n.v = n.v * n.t := by
    have he := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq01_xv
    have htt : n.t * n.t = 1 := by
      have hs : n.t ^ 2 = 1 := n.t_order ▸ pow_orderOf_eq_one n.t
      simpa only [pow_two] using hs
    have he' := congrArg (fun g : G => f.x⁻¹ * g * n.t) he
    simpa only [hA, mul_assoc, inv_mul_cancel_left, htt, mul_one] using he'.symm
  have hax : A f.a / f.a ∈ (commutator J).map ι := by
    have hm : Tits.parrottCommutator f.a f.x ∈ (commutator J).map ι := by
      rcases f.ax_alternative with he | he
      · rw [he]; exact one_mem _
      · rw [he]; exact f.basis_mem_derived n.t (by simp)
    have hh := derived_conjugate_mem
      (inv_mem (f.generators_mem_core f.a (by simp))) hm
    convert hh using 1
    rw [hA]
    simp only [Tits.parrottCommutator, div_eq_mul_inv]
    group
  obtain ⟨hbx, hcx, hdx, _⟩ := f.outer_images_mod_derived h
  have hDlift (j : J) (hj : ι j ∈ (commutator J).map ι) : j ∈ commutator J := by
    obtain ⟨k, hk, hkj⟩ := hj
    exact hι hkj ▸ hk
  obtain ⟨hZ, _, _, _, hupper, hElem, _, _⟩ := parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 (commutator J) := hElem
  have hh := intrinsic_covariance hupper R a b c d t v
    (hι (by simpa only [pc_map, ha, hb, ht] using f.eq05_ab))
    (hι (by simpa only [pc_map, hd, hb, hv] using f.eq03_db))
    (hι (by simpa only [map_pow, map_one, ha] using f.a_sq))
    (hι (by simpa only [map_pow, hb, hv] using f.eq03_b))
    (hι (by simpa only [hR, ht] using hAt))
    (hι (by simpa only [hR, map_mul, ht, hv] using hAv))
    (hDlift _ (by simpa only [map_div, hR, ha] using hax))
    (hDlift _ (by simpa only [map_div, map_mul, hR, hA, ha, hb] using hbx))
    (hDlift _ (by simpa only [map_div, map_mul, hR, hA, ha, hb, hc] using hcx))
    (hDlift _ (by simpa only [map_div, map_mul, hR, hA, ha, hb, hc, hd] using hdx))
  change (center J).map ι = zpowers z at hZ
  have transfer {j : J} (hj : j ∈ center J) : ι j ∈ zpowers z := by
    rw [← hZ]
    exact mem_map_of_mem ι hj
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [map_div, map_mul, pc_map, hR, ha, hc, hd, ht] using transfer hh.1
  · simpa only [map_div, map_mul, pc_map, hR, ha, hb, hc, hd] using transfer hh.2.1
  · simpa only [map_div, map_mul, pc_map, hR, ha, hd, ht] using transfer hh.2.2.1
  · simpa only [map_div, map_mul, map_pow, pc_map, hR, ha, hc, hd, hv] using transfer hh.2.2.2

end Stellmacher.Recognition.ParrottSylowInitialData
