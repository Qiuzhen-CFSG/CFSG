module

public import Stellmacher.Recognition.Parrott.NormalizerCoreOmega
public import Stellmacher.Recognition.Parrott.NormalizerInvolutionCosets
public import Stellmacher.Recognition.Parrott.OuterInvolutionClasses

/-!
# Transporting outer involutions through the second normalizer core

An outer involution in the actual normalizer core supplies two representatives,
y and yz. Both are outer involutions in that same core. The two-class theorem
in H and transport from the normalizer core into E then give transport for
every outer involution of the supplied Sylow, with the conjugator in H ∨ N.

The final theorem discharges both local calculations using the H-class cover
and the three-coset transport theorem. It applies to every outer involution of
the Sylow, without requiring membership in the normalizer core.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
p.674 (the representatives y and yz), and pp.677–678 (the three F-cosets).
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

omit [Finite G] in
/-- Multiplication by z preserves outer involutions in the actual normalizer
core. This retains the supplied core, rather than choosing a Sylow conjugate. -/
public theorem normalizer_core_outer_involution_mul_z
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let N := normalizer (d.F : Set G)
    let X := (pCore 2 N).map N.subtype
    ∀ y : G, y ∈ X → y ∉ J.map H.subtype → orderOf y = 2 →
      y * z ∈ X ∧ y * z ∉ J.map H.subtype ∧ orderOf (y * z) = 2 := by
  intro H J N X y hyX hyJ hy2
  have hzX : z ∈ X := d.le_normalizer_core d.z_mem_inf.2
  have hzJ : z ∈ J.map H.subtype := d.le_core d.z_mem_inf.2
  have hyH : y ∈ H := d.sylow_le_centralizer (d.normalizer_core_le_sylow hyX)
  have hyz : y * z = z * y := mem_centralizer_singleton_iff.mp hyH
  have hypow : y ^ 2 = 1 := hy2 ▸ pow_orderOf_eq_one y
  have hzpow : z ^ 2 = 1 := h.involution ▸ pow_orderOf_eq_one z
  have hout : y * z ∉ J.map H.subtype := by
    intro hh
    apply hyJ
    simpa only [mul_inv_cancel_right] using (J.map H.subtype).mul_mem hh
      ((J.map H.subtype).inv_mem hzJ)
  refine ⟨X.mul_mem hyX hzX, hout, orderOf_eq_prime ?_ ?_⟩
  · calc
      (y * z) ^ 2 = y ^ 2 * z ^ 2 := (show Commute y z from hyz).mul_pow 2
      _ = 1 := by rw [hypow, hzpow, one_mul]
  · intro hh
    exact hout (hh ▸ (J.map H.subtype).one_mem)

/-- There is a pair y, yz of outer involutions in the supplied normalizer core,
so a two-class cover may be applied to these particular representatives. -/
public theorem exists_normalizer_core_outer_involution_pair
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let N := normalizer (d.F : Set G)
    let X := (pCore 2 N).map N.subtype
    ∃ y : G, y ∈ X ∧ y ∉ J.map H.subtype ∧ orderOf y = 2 ∧
      y * z ∈ X ∧ y * z ∉ J.map H.subtype ∧ orderOf (y * z) = 2 := by
  intro H J N X
  obtain ⟨y, hyX, hy2, hyJ⟩ :=
    d.exists_normalizer_core_involution_outside_original_core h hN hproper
  exact ⟨y, hyX, hyJ, hy2, d.normalizer_core_outer_involution_mul_z h y hyX hyJ hy2⟩

/-- A normalizer conjugate of an outer involution which lies in E ∨ F must
lie in E. Involutions in that join belong to E or F, and N preserves F. -/
public theorem outer_involution_normalizer_conjugate_mem_derived
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    ∀ y : G, y ∉ J.map H.subtype → orderOf y = 2 →
      ∀ n : N, (n : G) * y * (n : G)⁻¹ ∈ E ⊔ d.F →
        (n : G) * y * (n : G)⁻¹ ∈ E := by
  intro H J E N y hyJ hy2 n hn
  have hyF : y ∉ d.F := fun hh => hyJ (d.le_core hh)
  have hpow : ((n : G) * y * (n : G)⁻¹) ^ 2 = 1 := by
    have hh := congrArg (MulAut.conj (n : G))
      (show y ^ 2 = 1 from hy2 ▸ pow_orderOf_eq_one y)
    simpa only [map_pow, map_one, MulAut.conj_apply] using hh
  rcases d.elementary_join_involution h _ hn hpow with he | hf
  · exact he
  · exact (hyF ((mem_normalizer_iff.mp n.property y).mpr hf)).elim

/-- The H-class cover and transport for outer involutions in the normalizer
core suffice for all outer involutions in the supplied Sylow. Both local
calculations are explicit premises of this assembly theorem. -/
public theorem outer_involution_transport_of_local_calculations
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let X := (pCore 2 N).map N.subtype
    let L := H ⊔ N
    (∀ y u : G, y ∈ H → y ∉ J.map H.subtype → orderOf y = 2 →
      u ∈ H → u ∉ J.map H.subtype → orderOf u = 2 →
      ∃ c : H, (c : G) * u * (c : G)⁻¹ = y ∨
        (c : G) * u * (c : G)⁻¹ = y * z) →
    (∀ y : G, y ∈ X → y ∉ J.map H.subtype → orderOf y = 2 →
      ∃ n : N, (n : G) * y * (n : G)⁻¹ ∈ E ⊔ d.F) →
    ∀ u : G, u ∈ (d.sylow : Subgroup G) → u ∉ J.map H.subtype →
      orderOf u = 2 → ∃ l : L, (l : G) * u * (l : G)⁻¹ ∈ E := by
  intro H J E N X L hclasses htransport u huT huJ hu2
  obtain ⟨y, hyX, hyJ, hy2, hyzX, hyzJ, hyz2⟩ :=
    d.exists_normalizer_core_outer_involution_pair h hN hproper
  obtain ⟨c, hc⟩ := hclasses y u
    (d.sylow_le_centralizer (d.normalizer_core_le_sylow hyX)) hyJ hy2
    (d.sylow_le_centralizer huT) huJ hu2
  have hstep (w : G) (hwX : w ∈ X) (hwJ : w ∉ J.map H.subtype)
      (hw2 : orderOf w = 2) (hcw : (c : G) * u * (c : G)⁻¹ = w) :
      ∃ l : L, (l : G) * u * (l : G)⁻¹ ∈ E := by
    obtain ⟨n, hnjoin⟩ := htransport w hwX hwJ hw2
    have hn := d.outer_involution_normalizer_conjugate_mem_derived h w hwJ hw2 n hnjoin
    refine ⟨⟨(n : G) * (c : G), L.mul_mem (mem_sup_right n.property)
      (mem_sup_left c.property)⟩, ?_⟩
    change ((n : G) * (c : G)) * u * ((n : G) * (c : G))⁻¹ ∈ E
    rw [mul_inv_rev]
    simpa only [← hcw, mul_assoc] using hn
  rcases hc with hc | hc
  · exact hstep y hyX hyJ hy2 hc
  · exact hstep (y * z) hyzX hyzJ hyz2 hc

/-- Every outer involution of the supplied Sylow is conjugate into the derived
core E by an element of H ∨ N. The H-class cover first transports it to one of
the two outer representatives in the normalizer core; the supplied Q then
transports that representative into E. -/
public theorem outer_involution_transport
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let X := (pCore 2 N).map N.subtype
    let D := (commutator X).map X.subtype
    let A := (Q : Subgroup N).map N.subtype
    let L := H ⊔ N
    X ⊓ centralizer (A : Set G) ≤ D →
    ∀ v : G, orderOf v = 2 → d.F ⊓ centralizer (A : Set G) = zpowers v →
    ∀ u : G, u ∈ (d.sylow : Subgroup G) → u ∉ J.map H.subtype →
      orderOf u = 2 → ∃ l : L, (l : G) * u * (l : G)⁻¹ ∈ E := by
  intro H J E N X D A L hCD v hv hfix
  exact d.outer_involution_transport_of_local_calculations h hN hproper
    (parrott_outer_involution_classes z h)
    (d.normalizer_core_outer_involution_conjugate_into_elementary_join
      h hN hproper Q hCD v hv hfix)

end Stellmacher.Recognition.ParrottSecondElementaryData
