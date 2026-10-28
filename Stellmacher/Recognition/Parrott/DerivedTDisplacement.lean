module

public import Stellmacher.Recognition.Parrott.ElementaryJoin
public import Stellmacher.Recognition.Parrott.DerivedTCentralizerCore
public import Theory.GroupAction.FiveFourSquareFixed
public import Theory.GroupAction.InvariantHyperplaneDisplacement
/-!
# The derived-core displacement in the first centralizer

For C=C_T(t) of order 1024, an element of C has order four modulo
J=O₂(C_G(z)). Its faithful action on J′/Z(J) has two fixed points.
The invariant hyperplane (E∩F)/⟨z⟩ is therefore the displacement image.
Displacements lift to commutators in C, and ⟨z⟩≤C′ supplies the kernel,
proving E∩F≤C′ without any additional characteristic geometry.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674 and the last two paragraphs of p.676.
-/

open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Stellmacher.Recognition.ParrottSecondElementaryData
/-- The fixed hyperplane lies in the actual derived subgroup of the first centralizer. -/
public theorem elementary_inf_le_t_centralizer_commutator
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ t ∈ E, t ∉ zpowers z →
      let C := (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G)
      Nat.card C = 1024 → E ⊓ d.F ≤ (commutator C).map C.subtype := by
  intro H J E t ht htz C hC
  let D := commutator J
  let Z := (center J).subgroupOf D
  let W := D ⧸ Z
  let i := H.subtype.comp J.subtype
  let ι := i.comp D.subtype
  let q := QuotientGroup.mk' Z
  obtain ⟨y, hyC, hyorder⟩ := d.t_centralizer_exists_quotient_order_four h t ht htz hC
  obtain ⟨hZmap, _, _, _, hUpper, hElem, hDcard, _⟩ := parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 D := hElem
  have hZD : center J ≤ D := by
    rw [show D = Subgroup.upperCentralSeries J 2 from hUpper]
    simpa only [Subgroup.upperCentralSeries_one] using
      Subgroup.upperCentralSeries_mono J (show 1 ≤ 2 by decide)
  have hZJcard : Nat.card (center J) = 2 := by
    have hh := card_map_of_injective (K := center J)
      (f := i) (H.subtype_injective.comp J.subtype_injective)
    rw [hZmap, Nat.card_zpowers, h.involution] at hh
    exact hh.symm
  have hZcard : Nat.card Z = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZD).toEquiv).trans hZJcard
  have hWcard : Nat.card W = 16 := by
    have hh := Z.index_mul_card
    change Nat.card W * Nat.card Z = Nat.card D at hh
    rw [hZcard, hDcard] at hh
    omega
  let : IsElementaryAbelian 2 W := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := (Group.exponent_quotient_dvd Z).trans
      (IsElementaryAbelian.exponent_dvd_p 2 D) }
  obtain ⟨f, hf, heval⟩ := parrott_derived_quotient_action z h
  let a : MulAut W := f (QuotientGroup.mk' J y)
  have haorder : orderOf a = 4 :=
    (orderOf_injective f hf (QuotientGroup.mk' J y)).trans hyorder
  have ha4 : a ^ 4 = 1 := haorder ▸ pow_orderOf_eq_one a
  obtain ⟨φ, hφ, ⟨e⟩⟩ := h.quotient_model
  have hfixed : Nat.card (FixedPoints.subgroup (zpowers a) W) = 2 := by
    have hh := (Theory.GroupAction.five_four_sixteen_order_four_fixed_cards hWcard φ hφ
      (f.comp e.symm.toMonoidHom) (hf.comp e.symm.injective)
      (e (QuotientGroup.mk' J y)) ((e.orderOf_eq _).trans hyorder)).1
    change Nat.card (FixedPoints.subgroup
      (zpowers (f (e.symm (e (QuotientGroup.mk' J y))))) W) = 2 at hh
    rw [e.symm_apply_apply] at hh
    exact hh
  let Y := zpowers y
  let : MulDistribMulAction Y J := conjMulDistribMulActionOfLeNormalizer Y J
    (le_normalizer_of_normal (H := J))
  let : IsInvariant Y J D := isInvariant_of_characteristic D
  let b : MulAut D := MulDistribMulAction.toMulAut Y D ⟨y, mem_zpowers y⟩
  have hcompat (u : D) : a (q u) = q (b u) := heval y u (b u) rfl
  have hι : Function.Injective ι :=
    (H.subtype_injective.comp J.subtype_injective).comp D.subtype_injective
  have hrange : ι.range = E := by
    rw [MonoidHom.range_comp, range_subtype]
  let U := d.F.comap ι
  have hUmap : U.map ι = E ⊓ d.F := by
    rw [map_comap_eq, hrange, inf_comm]
  have hUcard : Nat.card U = 16 := by
    rw [← card_map_of_injective (K := U) hι, hUmap]
    exact d.inf_card
  have hUindex : U.index = 2 := by
    have hh := U.card_mul_index
    rw [hUcard, hDcard] at hh
    omega
  have hZU : Z ≤ U := by
    intro u hu
    have hh : ι u ∈ zpowers z := hZmap ▸ mem_map_of_mem i hu
    exact (zpowers_le.mpr d.z_mem_inf.2) hh
  let V := U.map q
  have hVindex : V.index = 2 := by
    rw [index_map_eq U (QuotientGroup.mk'_surjective Z)
      (by simpa only [q, QuotientGroup.ker_mk'] using hZU), hUindex]
  have hstable : ∀ u ∈ V, a u ∈ V := by
    rintro _ ⟨u, hu, rfl⟩
    rw [hcompat]
    apply mem_map_of_mem
    change (y : G) * ι u * (y : G)⁻¹ ∈ d.F
    exact (mem_normalizer_iff.mp (d.sylow_le_normalizer hyC.1) (ι u)).mp hu
  obtain ⟨s, hs, hsrange⟩ := MulAut.displacement_range_eq_of_invariant_index_two
    a ha4 hfixed V hVindex hstable
  have hZlow := d.involution_line_le_t_centralizer_commutator h t ht htz
  have hElow := d.derived_le_t_centralizer h t ht
  intro x hx
  obtain ⟨u, hu, rfl⟩ := hx.1
  let uD : D := ⟨u, hu⟩
  have huV : q uD ∈ V := mem_map_of_mem q hx.2
  rw [← hsrange] at huV
  obtain ⟨w, hw⟩ := huV
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective Z w
  let δ := b c * c⁻¹
  have hδ : q δ = q uD := by
    have hinv : (q c)⁻¹ = q c := inv_eq_of_mul_eq_one_left (by
      simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 W) (q c))
    change q (b c * c⁻¹) = q uD
    rw [map_mul, map_inv, ← hcompat, hinv, ← hs]
    exact hw
  have hδlow : ι δ ∈ (commutator C).map C.subtype := by
    rw [map_subtype_commutator]
    exact commutator_mem_commutator hyC (hElow (mem_map_of_mem i c.property))
  have hdiff : uD / δ ∈ Z := QuotientGroup.eq_iff_div_mem.mp hδ.symm
  have hdiffLow : ι (uD / δ) ∈ (commutator C).map C.subtype := by
    apply hZlow
    rw [← hZmap]
    exact mem_map_of_mem i hdiff
  have hh := ((commutator C).map C.subtype).mul_mem hdiffLow hδlow
  rw [← map_mul, div_mul_cancel] at hh
  exact hh
end Stellmacher.Recognition.ParrottSecondElementaryData
