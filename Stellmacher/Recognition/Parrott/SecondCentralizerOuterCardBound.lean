module

public import Stellmacher.Recognition.Parrott.SecondCentralizerOuterSelection
public import Stellmacher.Recognition.Parrott.SecondCentralizerOriginalCoreCount

/-!
# The outer centralizer bound from the original core

Put N=N_G(F), K=O₂(N), W=Ω₁(K), H=C_G(z), and J=O₂(H).
An element of the supplied Sylow outside K fixes exactly ⟨z⟩ in Z(K).
Its N-centralizer therefore fixes z and lies in the supplied Sylow.

For an involution w outside W this centralizer actually lies in J.
Otherwise an element x outside J commuting with w fixes its image in J/J′.
The involution of the cyclic Sylow image of order four fixes that image too.
The original-core action calculation then makes w centralize Z(W), forcing
w into W. Thus both C_N(w) and C_N(v,w) can be computed in J.
The original-core calculation gives |C_J(w)|=32. Intersecting with C_G(v)
therefore gives the required bound |C_N(v,w)|≤32.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
pp.674 and 677–678, and §4, p.682. The cyclic quotient calculation follows
`NormalizerElementaryCentralizer`; the commuting-action step is supplied by
`OuterCoreFixedCentralization`.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSecondElementaryData
variable {G : Type*} [Group G] [Finite G] {z : G}
/-- Outside the second core, a Sylow element's normalizer centralizer lies
in the same supplied Sylow subgroup. -/
public theorem outside_core_normalizer_centralizer_le_sylow
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    ∀ w : G, w ∈ (d.sylow : Subgroup G) → w ∉ K.map N.subtype →
      N ⊓ centralizer ({w} : Set G) ≤ (d.sylow : Subgroup G) := by
  intro N K w hw hwK
  let Z := (center K).map (N.subtype.comp K.subtype)
  have hfixed : Z ⊓ centralizer ({w} : Set G) = zpowers z := by
    apply le_antisymm
    · intro t ht
      by_contra htz
      apply hwK
      rw [d.normalizer_core_eq_sylow_centralizer h hN hproper t ht.1 htz]
      exact ⟨hw, mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp ht.2).symm⟩
    · apply zpowers_le.mpr
      exact ⟨d.z_mem_normalizer_core_center, mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp (d.sylow_le_centralizer hw)).symm⟩
  intro x hx
  rw [← d.normalizer_inf_centralizer h]
  refine ⟨hx.1, ?_⟩
  rw [← normalizer_zpowers_eq_centralizer_of_order_two z h.involution, ← hfixed]
  exact inf_normalizer_le_normalizer_inf
    ⟨d.normalizer_core_centers_normalized.1 hx.1,
      (centralizer ({w} : Set G)).le_normalizer hx.2⟩

private theorem outside_omega_fixed_centralizer_eq_sylow_centralizer
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let W := (omega₁ K (p := 2)).map (N.subtype.comp K.subtype)
    ∀ v w : G, w ∈ (d.sylow : Subgroup G) → orderOf w = 2 → w ∉ W →
      (N ⊓ centralizer ({v} : Set G)) ⊓ centralizer ({w} : Set G) =
        ((d.sylow : Subgroup G) ⊓ centralizer ({v} : Set G)) ⊓
          centralizer ({w} : Set G) := by
  intro N K W v w hw hw2 hwW
  have hwK : w ∉ K.map N.subtype := by
    rintro ⟨wN, hwNK, heq⟩
    apply hwW
    refine ⟨⟨wN, hwNK⟩, ?_, heq⟩
    apply Subgroup.subset_closure
    apply Subtype.ext
    apply Subtype.ext
    change (wN : G) ^ (2 ^ 1) = 1
    change (wN : G) = w at heq
    rw [heq]
    simpa only [pow_one] using hw2 ▸ pow_orderOf_eq_one w
  apply le_antisymm
  · intro x hx
    exact ⟨⟨d.outside_core_normalizer_centralizer_le_sylow h hN hproper w hw hwK
      ⟨hx.1.1, hx.2⟩, hx.1.2⟩, hx.2⟩
  · exact inf_le_inf_right _ (inf_le_inf_right _ d.sylow_le_normalizer)


omit [Finite G] in
private theorem outer_card_quotient_involution_eq_or_square (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    ∀ x y : H, (x : G) ∈ (d.sylow : Subgroup G) →
      (y : G) ∈ (d.sylow : Subgroup G) → x ∉ J → orderOf y = 2 → y ∉ J →
      QuotientGroup.mk' J y = QuotientGroup.mk' J x ∨
        QuotientGroup.mk' J y = (QuotientGroup.mk' J x) ^ 2 := by
  intro H J x y hx hy hxJ hy2 hyJ
  let q := QuotientGroup.mk' J
  obtain ⟨φ, _, ⟨e⟩⟩ := h.quotient_model
  let M := SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ
  let : Finite M := Finite.of_equiv
    (Multiplicative (ZMod 5) × Multiplicative (ZMod 4)) SemidirectProduct.equivProd.symm
  let model := e.toMonoidHom.comp q
  let A := (d.localSylow : Subgroup H).map model
  obtain ⟨hcyc, hcard⟩ := SemidirectProduct.two_subgroup_isCyclic_card_dvd_four φ A
    (d.localSylow.isPGroup'.map model)
  let : IsCyclic A := hcyc
  have hmem (u : H) (hu : (u : G) ∈ (d.sylow : Subgroup G)) : model u ∈ A := by
    rw [d.sylow_map] at hu
    obtain ⟨v, hv, heq⟩ := hu
    exact mem_map_of_mem model ((H.subtype_injective heq) ▸ hv)
  let xA : A := ⟨model x, hmem x hx⟩
  let yA : A := ⟨model y, hmem y hy⟩
  have hne (u : H) (hu : u ∉ J) : model u ≠ 1 := by
    intro heq
    exact hu ((QuotientGroup.eq_one_iff u).mp
      (e.injective (heq.trans (map_one e).symm)))
  have hyA : orderOf yA = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      change model y ^ 2 = 1
      rw [← map_pow, show y ^ 2 = 1 from hy2 ▸ pow_orderOf_eq_one y, map_one]
    · exact fun hh => hne y hyJ (congrArg A.subtype hh)
  have hxord : orderOf xA = 2 ∨ orderOf xA = 4 := by
    have hd := (orderOf_dvd_natCard xA).trans hcard
    have hh : orderOf xA ∈ Nat.divisors 4 := Nat.mem_divisors.mpr ⟨hd, by decide⟩
    rw [show Nat.divisors 4 = {1, 2, 4} by decide] at hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with h1 | h2 | h4
    · exact (hne x hxJ (congrArg A.subtype (orderOf_eq_one_iff.mp h1))).elim
    · exact Or.inl h2
    · exact Or.inr h4
  rcases hxord with hx2 | hx4
  · left
    exact e.injective (congrArg A.subtype (IsCyclic.eq_of_orderOf_eq_two hyA hx2))
  · right
    have hx22 : orderOf (xA ^ 2) = 2 := by rw [orderOf_pow, hx4]; decide
    have hh := congrArg A.subtype (IsCyclic.eq_of_orderOf_eq_two hyA hx22)
    apply e.injective
    change e (q y) = e (q x) ^ 2 at hh
    simpa only [map_pow] using hh


open scoped commutatorElement

private theorem outside_omega_normalizer_centralizer_le_original_core
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let W := (omega₁ K (p := 2)).map (N.subtype.comp K.subtype)
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    ∀ w : G, w ∈ (d.sylow : Subgroup G) → orderOf w = 2 → w ∉ W →
      N ⊓ centralizer ({w} : Set G) ≤ J.map H.subtype := by
  intro N K W H J w hw hw2 hwW
  let U := omega₁ K (p := 2)
  let ZU := (center U).map ((N.subtype.comp K.subtype).comp U.subtype)
  let E := (commutator J).map (H.subtype.comp J.subtype)
  have hwJ : w ∈ J.map H.subtype := by
    by_contra hn
    exact hwW (d.sylow_outer_involution_mem_normalizer_omega h hN hproper w hw hw2 hn)
  obtain ⟨wH, hwHJ, hwH⟩ := hwJ
  change (wH : G) = w at hwH
  let wJ : J := ⟨wH, hwHJ⟩
  obtain ⟨y, hyK, hy2, hyJ⟩ :=
    d.exists_normalizer_core_involution_outside_original_core h hN hproper
  have hyT := d.normalizer_core_le_sylow hyK
  let yH : H := ⟨y, d.sylow_le_centralizer hyT⟩
  have hyH2 : orderOf yH = 2 := (Subgroup.orderOf_coe yH).symm.trans hy2
  have hyHJ : yH ∉ J := fun hh => hyJ (mem_map_of_mem H.subtype hh)
  have hfixed : E ⊓ centralizer ({y} : Set G) = ZU := by
    apply eq_of_le_of_card_ge
      (d.sylow_outer_derived_fixed_le_omega_center h hN hproper y hyT hyJ)
    rw [d.normalizer_core_outer_fixed_card h y hyK hy2 hyJ,
      card_map_of_injective ((N.subtype_injective.comp K.subtype_injective).comp
        U.subtype_injective), (d.normalizer_core_omega_structure h hN hproper).2.1]
  intro x hx
  have hxT : x ∈ (d.sylow : Subgroup G) := by
    have hh := d.outside_omega_fixed_centralizer_eq_sylow_centralizer
      h hN hproper w w hw hw2 hwW
    have hx' : x ∈ (N ⊓ centralizer ({w} : Set G)) ⊓ centralizer ({w} : Set G) :=
      ⟨hx, hx.2⟩
    rw [hh] at hx'
    exact hx'.1.1
  by_contra hxJ
  let xH : H := ⟨x, d.sylow_le_centralizer hxT⟩
  have hxHJ : xH ∉ J := fun hh => hxJ (mem_map_of_mem H.subtype hh)
  obtain ⟨f, _, heval⟩ := parrott_core_quotient_action z h
  let q := QuotientGroup.mk' (commutator J)
  let qJ := QuotientGroup.mk' J
  have hfx : f (qJ xH) (q wJ) = q wJ := by
    apply heval xH wJ wJ
    apply H.subtype_injective
    change (wH : G) = x * (wH : G) * x⁻¹
    rw [hwH]
    exact (mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hx.2)).symm
  have hfy : f (qJ yH) (q wJ) = q wJ := by
    rcases d.outer_card_quotient_involution_eq_or_square h xH yH hxT hyT
      hxHJ hyH2 hyHJ with he | he
    · rw [he]; exact hfx
    · rw [he, map_pow, pow_two, MulAut.mul_apply, hfx, hfx]
  let wy : J := ⟨yH * wH * yH⁻¹, (inferInstance : J.Normal).conj_mem wH hwHJ yH⟩
  have hqeq : q wy = q wJ := (heval yH wJ wy rfl).symm.trans hfy
  have hcomm : ⁅wH, yH⁆ ∈ (commutator J).map J.subtype := by
    have hm := mem_map_of_mem J.subtype (QuotientGroup.eq_iff_div_mem.mp hqeq.symm)
    change wH / (yH * wH * yH⁻¹) ∈ (commutator J).map J.subtype at hm
    convert hm using 1
    simp only [commutatorElement_def, div_eq_mul_inv]
    group
  have hwC : w ∈ centralizer (ZU : Set G) := by
    rw [← hfixed]
    intro a ha
    obtain ⟨aJ, haJ, heq⟩ := ha.1
    change (aJ : G) = a at heq
    have hay : Commute (aJ : H) yH := by
      apply H.subtype_injective
      change (aJ : G) * y = y * (aJ : G)
      rw [heq]
      exact mem_centralizer_singleton_iff.mp ha.2
    have hh := parrott_outer_core_centralizes_derived_fixed_of_commutator_mem z h
      yH hyH2 hyHJ wH hwHJ hcomm aJ (mem_map_of_mem J.subtype haJ) hay
    have hhG := congrArg H.subtype hh.symm.eq
    change (aJ : G) * (wH : G) = (wH : G) * (aJ : G) at hhG
    rwa [hwH, heq] at hhG
  have heq : N ⊓ centralizer (ZU : Set G) = W :=
    d.normalizer_omega_center_centralizer h hN hproper
  exact hwW (heq ▸ ⟨d.sylow_le_normalizer hw, hwC⟩)

/-- For an involution in the supplied Sylow outside omega, its full
N-centralizer equals its centralizer in the original core. -/
public theorem outside_omega_normalizer_centralizer_eq_original_core
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let W := (omega₁ K (p := 2)).map (N.subtype.comp K.subtype)
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    ∀ w : G, w ∈ (d.sylow : Subgroup G) → orderOf w = 2 → w ∉ W →
      N ⊓ centralizer ({w} : Set G) =
        J.map H.subtype ⊓ centralizer ({w} : Set G) := by
  intro N K W H J w hw hw2 hwW
  apply le_antisymm
  · exact le_inf (d.outside_omega_normalizer_centralizer_le_original_core
      h hN hproper w hw hw2 hwW) inf_le_right
  · exact inf_le_inf_right _ (d.core_le_sylow.trans d.sylow_le_normalizer)

/-- Intersecting with the prescribed fixed involution's centralizer reduces
C_V(w) to a simultaneous centralizer wholly inside the original core. -/
public theorem outside_omega_fixed_centralizer_eq_original_core
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let W := (omega₁ K (p := 2)).map (N.subtype.comp K.subtype)
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    ∀ v w : G, w ∈ (d.sylow : Subgroup G) → orderOf w = 2 → w ∉ W →
      (N ⊓ centralizer ({v} : Set G)) ⊓ centralizer ({w} : Set G) =
        (J.map H.subtype ⊓ centralizer ({v} : Set G)) ⊓
          centralizer ({w} : Set G) := by
  intro N K W H J v w hw hw2 hwW
  rw [inf_right_comm N, d.outside_omega_normalizer_centralizer_eq_original_core
    h hN hproper w hw hw2 hwW, inf_right_comm]

/-- The simultaneous centralizer of the prescribed fixed involution and an
outside-omega involution has order at most 32. -/
public theorem outside_omega_fixed_centralizer_card_le
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let W := (omega₁ K (p := 2)).map (N.subtype.comp K.subtype)
    let V := N ⊓ centralizer ({v} : Set G)
    let P := (d.sylow : Subgroup G) ⊓ centralizer ({v} : Set G)
    ∀ w : G, w ∈ P → orderOf w = 2 → w ∉ W →
      Nat.card (V ⊓ centralizer ({w} : Set G) : Subgroup G) ≤ 32 := by
  intro N K W V P w hw hw2 hwW
  change Nat.card ((N ⊓ centralizer ({v} : Set G)) ⊓
    centralizer ({w} : Set G) : Subgroup G) ≤ 32
  rw [d.outside_omega_fixed_centralizer_eq_original_core h hN hproper
    v w hw.1 hw2 hwW]
  exact (card_le_of_le (inf_le_inf_right _ inf_le_left)).trans_eq
    (d.outside_omega_original_core_centralizer_card h hN hproper Q v hv hfix
      w hw hw2 hwW)

/-- The centralizer-bound premise for the selected inverter in the fixed-join
witness assembly. The stronger outside-omega bound does not require inversion. -/
public theorem normalizer_fixed_inverter_centralizer_card_le
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let W := (omega₁ K (p := 2)).map (N.subtype.comp K.subtype)
    let A := (Q : Subgroup N).map N.subtype
    let V := N ⊓ centralizer ({v} : Set G)
    let P := (d.sylow : Subgroup G) ⊓ centralizer ({v} : Set G)
    ∀ w : G, w ∈ P → orderOf w = 2 → w ∉ W →
      (∀ a ∈ A, w * a * w⁻¹ = a⁻¹) →
      Nat.card (V ⊓ centralizer ({w} : Set G) : Subgroup G) ≤ 32 := by
  intro N K W A V P w hw hw2 hwW _
  exact d.outside_omega_fixed_centralizer_card_le h hN hproper Q v hv hfix w hw hw2 hwW

end Stellmacher.Recognition.ParrottSecondElementaryData
