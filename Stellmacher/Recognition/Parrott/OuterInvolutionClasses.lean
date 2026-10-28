module
public import Stellmacher.Recognition.Parrott.CentralizerStructure
public import Stellmacher.Recognition.Parrott.FiveNormalizerInvolutionClasses
public import Theory.GroupTheory.Involution.OddRotation

/-!
# The two-representative cover for outer involution classes

For H=C_G(z) with Parrott's centralizer hypotheses, an involution outside
J=O₂(H) inverts an element of order five. Thus it is H-conjugate into the
normalizer of any supplied Sylow-five subgroup P.

The class-cover reduction retains any supplied outer involution y: transport
both y and u into N_H(P), use the local two-representative cover there, and
conjugate back. Since z is central in H, the second representative becomes yz.
The centralizer hypothesis supplies P for the local class calculation in
`FiveNormalizerInvolutionClasses`, completing the unconditional H-class cover.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.674, final paragraph.
-/

open Subgroup BenderSuzuki.PFAppendixIII
open scoped Pointwise
namespace Stellmacher.Recognition

/-- Every outer involution is conjugate into the normalizer of the supplied
Sylow-five subgroup. -/
public theorem parrott_outer_involution_conjugate_into_five_normalizer
    {G : Type*} [Group G] [Finite G] (z : G)
    (h : ParrottCentralizerHypotheses z)
    (P : Sylow 5 (centralizer ({z} : Set G))) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    ∀ u : H, u ∉ J → orderOf u = 2 →
      ∃ a : H, a * u * a⁻¹ ∈ normalizer (P : Set H) := by
  intro H J u huJ hu2
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hui : IsInvolution u := by
    exact ⟨fun hh => by simp [hh] at hu2, hu2 ▸ pow_orderOf_eq_one u⟩
  obtain ⟨q, hq, hq2, r, hr, hur⟩ :=
    BenderSuzuki.involution_outside_twoCore_inverts_odd_prime u hui huJ
  have hqdiv : q ∣ 10240 := by
    rw [← (ParrottCentralizerHypotheses.card_and_solvable z h).1, ← hr]
    exact orderOf_dvd_natCard r
  have hq5 : q = 5 := by
    rw [show 10240 = 2 ^ 11 * 5 by decide] at hqdiv
    rcases hq.dvd_mul.mp hqdiv with hh | hh
    · have hh' : q ∣ 2 := hq.dvd_of_dvd_pow hh
      rcases (Nat.dvd_prime Nat.prime_two).mp hh' with hh' | hh'
      · exact (hq.ne_one hh').elim
      · exact (hq2 hh').elim
    · rcases (Nat.dvd_prime Nat.prime_five).mp hh with hh | hh
      · exact (hq.ne_one hh).elim
      · exact hh
  have hr5 : orderOf r = 5 := hr.trans hq5
  have hR : IsPGroup 5 (zpowers r) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hr5, pow_one])
  obtain ⟨Q, hRQ⟩ := hR.exists_le_sylow
  have hQcard : Nat.card Q = 5 := by
    rw [Q.card_eq_multiplicity, (ParrottCentralizerHypotheses.card_and_solvable z h).1]
    decide +kernel
  have hRQeq : zpowers r = (Q : Subgroup H) :=
    eq_of_le_of_card_ge hRQ (by rw [Nat.card_zpowers, hr5, hQcard])
  have hur' : (MulAut.conj u) r = r⁻¹ := by
    simpa only [MulAut.conj_apply, rightConjugateElem, hui.inv_eq_self] using hur
  have huN : u ∈ normalizer (Q : Set H) := by
    rw [← Q.coe_coe, ← hRQeq, mem_normalizer_iff]
    intro v
    have hforward : ∀ v : H, v ∈ zpowers r → u * v * u⁻¹ ∈ zpowers r := by
      intro v hv
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hv
      change (MulAut.conj u) (r ^ n) ∈ zpowers r
      rw [map_zpow, hur']
      exact zpow_mem ((zpowers r).inv_mem (mem_zpowers r)) n
    constructor
    · exact hforward v
    · intro hv
      have hh := hforward _ hv
      have heq : u * (u * v * u⁻¹) * u⁻¹ = v := by
        rw [hui.inv_eq_self]
        calc
          u * (u * v * u) * u = (u * u) * v * (u * u) := by group
          _ = v := by rw [← pow_two, hui.sq_eq_one]; simp
      rwa [heq] at hh
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq H Q P
  refine ⟨a, Sylow.smul_eq_iff_mem_normalizer.mp ?_⟩
  rw [← ha, ← mul_smul]
  have heq : a * u * a⁻¹ * a = a * u := by group
  rw [heq, mul_smul, Sylow.smul_eq_iff_mem_normalizer.mpr huN]
private theorem outer_involution_classes_of_normalizer
    {G : Type*} [Group G] [Finite G] (z : G)
    (P : Sylow 5 (centralizer ({z} : Set G))) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let N := normalizer (P : Set H)
    (∀ u : H, u ∉ J → orderOf u = 2 →
      ∃ a : H, a * u * a⁻¹ ∈ N) →
    (∀ y u : H, y ∈ N → y ∉ J → orderOf y = 2 →
      u ∈ N → u ∉ J → orderOf u = 2 →
      ∃ c : H, c * u * c⁻¹ = y ∨
        (c : G) * (u : G) * (c : G)⁻¹ = (y : G) * z) →
    ∀ y u : G, y ∈ H → y ∉ J.map H.subtype → orderOf y = 2 →
      u ∈ H → u ∉ J.map H.subtype → orderOf u = 2 →
      ∃ c : H, (c : G) * u * (c : G)⁻¹ = y ∨
        (c : G) * u * (c : G)⁻¹ = y * z := by
  intro H J N hreach hlocal y u hyH hyJ hy2 huH huJ hu2
  let yH : H := ⟨y, hyH⟩
  let uH : H := ⟨u, huH⟩
  have hyJ' : yH ∉ J := fun hh => hyJ (mem_map_of_mem H.subtype hh)
  have huJ' : uH ∉ J := fun hh => huJ (mem_map_of_mem H.subtype hh)
  have hy2' : orderOf yH = 2 := by rwa [← orderOf_injective H.subtype H.subtype_injective]
  have hu2' : orderOf uH = 2 := by rwa [← orderOf_injective H.subtype H.subtype_injective]
  obtain ⟨a, ha⟩ := hreach yH hyJ' hy2'
  obtain ⟨b, hb⟩ := hreach uH huJ' hu2'
  have hnot (v g : H) (hv : v ∉ J) : g * v * g⁻¹ ∉ J := by
    intro hh
    have := (inferInstance : J.Normal).conj_mem _ hh g⁻¹
    exact hv (by simpa [mul_assoc] using this)
  have horder (v g : H) (hv : orderOf v = 2) : orderOf (g * v * g⁻¹) = 2 := by
    simpa only [MulAut.conj_apply] using (MulAut.conj g).orderOf_eq v |>.trans hv
  obtain ⟨c, hc⟩ := hlocal _ _ ha (hnot yH a hyJ') (horder yH a hy2')
    hb (hnot uH b huJ') (horder uH b hu2')
  refine ⟨a⁻¹ * c * b, ?_⟩
  have haz : (a : G) * z = z * (a : G) :=
    mem_centralizer_singleton_iff.mp a.property
  rcases hc with hc | hc
  · left
    have hh := congrArg (fun v : H => ((a⁻¹ * v * a : H) : G)) hc
    simpa [mul_assoc, yH, uH] using hh
  · right
    have hh := congrArg (fun v : G => (a : G)⁻¹ * v * (a : G)) hc
    simpa [mul_assoc, yH, uH, ← haz] using hh

/-- The two-representative calculation inside a supplied Sylow-five normalizer
implies the H-class cover for any supplied outer involution y. -/
public theorem parrott_outer_involution_classes_of_normalizer
    {G : Type*} [Group G] [Finite G] (z : G)
    (h : ParrottCentralizerHypotheses z)
    (P : Sylow 5 (centralizer ({z} : Set G))) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let N := normalizer (P : Set H)
    (∀ y u : H, y ∈ N → y ∉ J → orderOf y = 2 →
      u ∈ N → u ∉ J → orderOf u = 2 →
      ∃ c : H, c * u * c⁻¹ = y ∨
        (c : G) * (u : G) * (c : G)⁻¹ = (y : G) * z) →
    ∀ y u : G, y ∈ H → y ∉ J.map H.subtype → orderOf y = 2 →
      u ∈ H → u ∉ J.map H.subtype → orderOf u = 2 →
      ∃ c : H, (c : G) * u * (c : G)⁻¹ = y ∨
        (c : G) * u * (c : G)⁻¹ = y * z := by
  exact outer_involution_classes_of_normalizer z P
    (parrott_outer_involution_conjugate_into_five_normalizer z h P)

/-- Every outer involution is H-conjugate to y or yz for any supplied outer
involution y. No global simplicity or N₂ hypothesis is needed. -/
public theorem parrott_outer_involution_classes
    {G : Type*} [Group G] [Finite G] (z : G)
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    ∀ y u : G, y ∈ H → y ∉ J.map H.subtype → orderOf y = 2 →
      u ∈ H → u ∉ J.map H.subtype → orderOf u = 2 →
      ∃ c : H, (c : G) * u * (c : G)⁻¹ = y ∨
        (c : G) * u * (c : G)⁻¹ = y * z := by
  obtain ⟨P, hP⟩ := h.five_centralizer
  exact parrott_outer_involution_classes_of_normalizer z h P
    (parrott_five_normalizer_involution_classes z h P hP)

end Stellmacher.Recognition
