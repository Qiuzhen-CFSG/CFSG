module

public import Stellmacher.Recognition.Parrott.SylowABGeometry
public import Stellmacher.Recognition.Parrott.SylowActionFrame
public import Theory.GroupAction.BinaryQuadraticPairing

/-!
# Square-displacement inputs for the b,w alignment

An action frame has an outer square outside the original core: its commutator
with w is v, whereas a core element has central commutator with every element
of the derived core. Thus its image in H/J has order four. The same equation
identifies the square of the supplied b with this square displacement.

These facts supply the marked inputs for the equivariant quadratic-map route
to equation (2). They do not yet assert the required orthogonality of b and w.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
printed p.678, equations (1)–(2), and the core geometry on pp.673–674.
-/

open Subgroup
open scoped commutatorElement
namespace Stellmacher.Recognition

variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

set_option quotPrecheck false in
local notation "H" => centralizer ({z} : Set G)
set_option quotPrecheck false in
local notation "J" => pCore 2 H
set_option quotPrecheck false in
local notation "E" => (commutator J).map ((H).subtype.comp (J).subtype)

private theorem core_derived_pc (h : ParrottCentralizerHypotheses z)
    {g k : G} (hg : g ∈ (J).map (H).subtype) (hk : k ∈ E) :
    Tits.parrottCommutator g k ∈ zpowers z := by
  let embed := (H).subtype.comp (J).subtype
  obtain ⟨gH, hgK, rfl⟩ := hg
  obtain ⟨kK, hkK, rfl⟩ := hk
  obtain ⟨hZ, _, _, _, hUpper, _, _, _⟩ := parrott_centralizer_structure z h
  have hcomm : ⁅commutator J, (⊤ : Subgroup J)⁆ ≤ center J := by
    rw [hUpper]
    simpa only [Subgroup.upperCentralSeries_one] using
      commutator_upperCentralSeries_top_le J 1
  have hh := mem_map_of_mem embed (hcomm (commutator_mem_commutator
    ((commutator J).inv_mem hkK) (show (⟨gH, hgK⟩ : J)⁻¹ ∈ ⊤ from mem_top _)))
  rw [hZ] at hh
  have heq : embed ⁅kK⁻¹, (⟨gH, hgK⟩ : J)⁻¹⁆ =
      (Tits.parrottCommutator (gH : G) (embed kK))⁻¹ := by
    simp only [commutatorElement_def, Tits.parrottCommutator,
      mul_inv_rev, inv_inv, map_mul, map_inv]
    change (embed kK)⁻¹ * (gH : G)⁻¹ * embed kK * (gH : G) = _
    group
  rw [heq] at hh
  simpa only [inv_inv, embed, Subgroup.coe_subtype] using (zpowers z).inv_mem hh

/-- The outer square of any marked action frame is outside the original core. -/
public theorem ParrottSylowActionData.square_not_mem_original_core
    (f : ParrottSylowActionData n) (h : ParrottCentralizerHypotheses z) :
    f.x ^ 2 ∉ (J).map (H).subtype := by
  intro hx
  have hw : f.w ∈ E := by
    rw [← f.derived_basis]
    exact subset_closure (by simp)
  have hv := core_derived_pc h hx hw
  rw [f.square_commutator_w] at hv
  apply n.v_not_mem_core_center
  rw [n.core_center_eq]
  exact mem_sup_left hv

/-- Retain the literal outer generator while exhibiting its order-four
quotient image and the square-displacement identity for the supplied b. -/
public theorem ParrottSylowActionData.bw_square_displacement_inputs
    (f : ParrottSylowActionData n) (h : ParrottCentralizerHypotheses z) :
    ∃ xH : H, (xH : G) = f.x ∧
      orderOf (QuotientGroup.mk' J xH) = 4 ∧
      n.b ∈ (J).map (H).subtype ∧ f.w ∈ E ∧
      n.b ^ 2 = Tits.parrottCommutator ((xH : G) ^ 2) f.w ∧
      n.b ^ 2 ∉ zpowers z := by
  have hxT : f.x ∈ (e.sylow : Subgroup G) := by
    rw [f.sylow_eq]
    exact mem_sup_left (mem_zpowers _)
  have hTH : (e.sylow : Subgroup G) ≤ H := by
    rw [e.sylow_map]
    exact map_subtype_le _
  let xH : H := ⟨f.x, hTH hxT⟩
  let q := QuotientGroup.mk' J
  have hfour : q xH ^ 4 = 1 := by
    rw [← map_pow]
    have hx4 : xH ^ 4 = 1 := Subtype.ext f.eq01_x
    rw [hx4, map_one]
  have htwo : q xH ^ 2 ≠ 1 := by
    intro heq
    have hj : xH ^ 2 ∈ J := (QuotientGroup.eq_one_iff _).mp (show q (xH ^ 2) = 1 by
      rw [map_pow]; exact heq)
    exact f.square_not_mem_original_core h (mem_map_of_mem (H).subtype hj)
  have horder : orderOf (q xH) = 4 := by
    have hdvd := orderOf_dvd_of_pow_eq_one hfour
    have hn : ¬ orderOf (q xH) ∣ 2 := fun hh => htwo (orderOf_dvd_iff_pow_eq_one.mp hh)
    have hle : orderOf (q xH) ≤ 4 := Nat.le_of_dvd (by decide) hdvd
    interval_cases ho : orderOf (q xH) <;> norm_num [ho] at *
  refine ⟨xH, rfl, horder, (n.three_generator_b_properties h).1, ?_, ?_, ?_⟩
  · rw [← f.derived_basis]
    exact subset_closure (by simp)
  · exact n.b_sq.trans f.square_commutator_w.symm
  · rw [n.b_sq]
    intro hv
    apply n.v_not_mem_core_center
    rw [n.core_center_eq]
    exact mem_sup_left hv

end Stellmacher.Recognition
