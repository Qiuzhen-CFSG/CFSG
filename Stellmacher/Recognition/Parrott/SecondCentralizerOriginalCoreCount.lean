module

public import Stellmacher.Recognition.Parrott.SecondCentralizerOuterSelection
public import Theory.GroupAction.Order512FiveCentralizer

/-!
# The selected inverter's original-core centralizer

The intrinsic order-five commutator pairing shows that any element of J
commuting with an element outside J′ lies in one of the two derived cosets
represented by 1 and that element. For the supplied involution a this puts
the entire core centralizer in F=⟨a⟩C_{J′}(a), giving C_J(a)=F.

The existing outside-omega transport provides compatible elementary data
with a=w. Its fixed join has order 32, so |C_J(w)|=32. In particular,
further intersection with C_G(v) has order at most 32.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674, p.678 (C_J(a)=F), and §4, p.682.
-/

open Subgroup
open scoped IsMulCommutative

namespace Stellmacher.Recognition.ParrottSecondElementaryData
variable {G : Type*} [Group G] [Finite G] {z : G}

omit [Finite G] in
private theorem original_core_centralizer_eq_fixed_join_of_derived_cosets
    (d : ParrottSecondElementaryData z)
    (hcosets : let H := centralizer ({z} : Set G)
      let J := pCore 2 H
      let a : J := ⟨d.a, d.a_mem_core⟩
      ∀ x : J, Commute a x →
        x ∈ commutator J ∨ a * x ∈ commutator J) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    J.map H.subtype ⊓ centralizer ({(d.a : G)} : Set G) = d.F := by
  intro H J
  let E := (commutator J).map (H.subtype.comp J.subtype)
  let a : J := ⟨d.a, d.a_mem_core⟩
  have hEF : E ⊓ centralizer ({(d.a : G)} : Set G) ≤ d.F := by
    rw [← d.inf_eq]
    exact inf_le_right
  have haF : (d.a : G) ∈ d.F := by
    rw [d.fixed_join]
    exact mem_sup_left (mem_zpowers _)
  apply le_antisymm
  · rintro x ⟨⟨xH, hxJ, hxval⟩, hxc⟩
    change (xH : G) = x at hxval
    let y : J := ⟨xH, hxJ⟩
    have hcomm : Commute a y := by
      apply Subtype.ext
      apply Subtype.ext
      change (d.a : G) * (xH : G) = (xH : G) * (d.a : G)
      rw [hxval]
      exact (mem_centralizer_singleton_iff.mp hxc).symm
    rcases hcosets y hcomm with hyD | hayD
    · exact hEF ⟨⟨y, hyD, hxval⟩, hxc⟩
    · have haxE : (d.a : G) * x ∈ E := by
        refine ⟨a * y, hayD, ?_⟩
        change (d.a : G) * (xH : G) = (d.a : G) * x
        rw [hxval]
      have haxF : (d.a : G) * x ∈ d.F := hEF ⟨haxE,
        (centralizer ({(d.a : G)} : Set G)).mul_mem
          (mem_centralizer_singleton_iff.mpr rfl) hxc⟩
      simpa only [inv_mul_cancel_left] using d.F.mul_mem (d.F.inv_mem haF) haxF
  · let : IsElementaryAbelian 2 d.F := d.elementary
    intro x hx
    exact ⟨d.le_core hx, mem_centralizer_singleton_iff.mpr (setLike_mul_comm hx haF)⟩

/-- The centralizer of the supplied involution in the original core is exactly
its elementary fixed join, including all elements of higher order. -/
public theorem original_core_centralizer_eq_fixed_join
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    J.map H.subtype ⊓ centralizer ({(d.a : G)} : Set G) = d.F := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  obtain ⟨P, hP⟩ := h.five_centralizer
  let _ : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let _ : MulDistribMulAction P J :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (P : Subgroup H) J
      (Subgroup.le_normalizer_of_normal (H := J))
  have hfixed : FixedPoints.subgroup P J ≤ center J := by
    intro x hx
    apply hP
    change (x : H) ∈ centralizer (P : Set H)
    intro a ha
    have hh := congrArg J.subtype (hx ⟨a, ha⟩)
    change a * (x : H) * a⁻¹ = x at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hPcard : Nat.card P = 5 := by
    rw [P.card_eq_multiplicity, (h.card_and_solvable z).1]
    decide +kernel
  apply d.original_core_centralizer_eq_fixed_join_of_derived_cosets
  dsimp only
  intro x hx
  apply Theory.GroupAction.parrott_commuting_derived_cosets
    pCore_isPGroup h.core_card h.core_class hPcard hfixed _ x ?_ hx
  exact fun hh => d.a_not_mem_derived (mem_map_of_mem J.subtype hh)

/-- Every supplied outside-omega involution has original-core centralizer
of order exactly 32. The inversion and derived-centralizer hypotheses used
in selecting it are unnecessary for this count. -/
public theorem outside_omega_original_core_centralizer_card
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let W := (omega₁ K (p := 2)).map (N.subtype.comp K.subtype)
    let P := (d.sylow : Subgroup G) ⊓ centralizer ({v} : Set G)
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let Y := J.map H.subtype
    ∀ w : G, w ∈ P → orderOf w = 2 → w ∉ W →
      Nat.card (Y ⊓ centralizer ({w} : Set G) : Subgroup G) = 32 := by
  intro N K W P H J Y w hw hw2 hwW
  obtain ⟨e, hew, _, _, _, _⟩ :=
    d.normalizer_fixed_outside_omega_fixed_join h hN hproper Q v hv hfix w hw hw2 hwW
  have he := e.original_core_centralizer_eq_fixed_join h
  change Y ⊓ centralizer ({(e.a : G)} : Set G) = e.F at he
  rw [hew] at he
  rw [he, e.card]

end Stellmacher.Recognition.ParrottSecondElementaryData
