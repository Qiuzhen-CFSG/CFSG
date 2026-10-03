module

public import Stellmacher.Recognition.Parrott.SylowSeedFrame

/-!
# Selecting three core generators before completing the dual basis

The initial construction separates into the compatible choices of `a,b,d`
through (8), and the choice of `c` with prescribed action on the derived
group. The latter step must also prove that the four elements generate the
actual core. This interface retains the original `z,t,v,F,T` throughout.

The involution already supplied with F completes every action frame's
elementary basis and has commutator z with w. Thus this first part of (2)
requires no further choice. The remaining selection must arrange the
relations with b, d, and x simultaneously.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed pp.678–679, equations (2)–(10).
-/

open Subgroup
open scoped commutatorElement
namespace Stellmacher.Recognition

variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

set_option quotPrecheck false in
local notation "H" => centralizer ({z} : Set G)
set_option quotPrecheck false in
local notation "J" => (pCore 2 H).map (H).subtype
set_option quotPrecheck false in
local notation "E" => (commutator (pCore 2 H)).map ((H).subtype.comp (pCore 2 H).subtype)

/-- The original involution supplied with F completes the action basis. -/
public theorem ParrottSylowActionData.original_elementary_basis
    (f : ParrottSylowActionData n) :
    closure ({z, n.t, n.v, f.u, (e.a : G)} : Set G) = e.F := by
  rw [show ({z, n.t, n.v, f.u, (e.a : G)} : Set G) =
      {z, n.t, n.v, f.u} ∪ {(e.a : G)} by
        ext g
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
        tauto,
    Subgroup.closure_union, ← zpowers_eq_closure, f.inf_basis,
    e.inf_eq, sup_comm, ← e.fixed_join]

/-- The a,w equation is forced by the actual fixed hyperplane E ∩ F. -/
public theorem ParrottSylowActionData.original_a_commutator_w [Finite G]
    (f : ParrottSylowActionData n) (h : ParrottCentralizerHypotheses z) :
    Tits.parrottCommutator (e.a : G) f.w = z := by
  classical
  let K := pCore 2 H
  let embed := (H).subtype.comp K.subtype
  have hw : f.w ∈ E := by
    rw [← f.derived_basis]
    exact subset_closure (by simp)
  obtain ⟨w, hwD, hwG⟩ := hw
  let a : K := ⟨e.a, e.a_mem_core⟩
  obtain ⟨hZ, _, _, _, hUpper, _, _, _⟩ := parrott_centralizer_structure z h
  have hcomm : ⁅commutator K, (⊤ : Subgroup K)⁆ ≤ center K := by
    rw [hUpper]
    simpa only [Subgroup.upperCentralSeries_one] using
      commutator_upperCentralSeries_top_le K 1
  have hc : Tits.parrottCommutator (e.a : G) f.w ∈ zpowers z := by
    have hm := mem_map_of_mem embed
      (hcomm (commutator_mem_commutator
        ((commutator K).inv_mem hwD) (show a⁻¹ ∈ (⊤ : Subgroup K) from mem_top _)))
    rw [hZ] at hm
    have heq : embed ⁅w⁻¹, a⁻¹⁆ =
        (Tits.parrottCommutator (e.a : G) f.w)⁻¹ := by
      simp only [commutatorElement_def,
        Tits.parrottCommutator, mul_inv_rev, inv_inv]
      change (embed w)⁻¹ * (e.a : G)⁻¹ * embed w * (e.a : G) = _
      rw [hwG]
      group
    rw [heq] at hm
    simpa only [inv_inv] using (zpowers z).inv_mem hm
  have hne : Tits.parrottCommutator (e.a : G) f.w ≠ 1 := by
    intro heq
    have hwa : f.w ∈ centralizer ({(e.a : G)} : Set G) :=
      mem_centralizer_singleton_iff.mpr
        ((Tits.parrottCommutator_eq_one_iff _ _).mp heq).symm.eq
    have hwF : f.w ∈ e.F := by
      have hh : f.w ∈ E ⊓ centralizer ({(e.a : G)} : Set G) :=
        ⟨hwG ▸ mem_map_of_mem embed hwD, hwa⟩
      rw [← e.inf_eq] at hh
      exact hh.2
    have hEF : E ≤ e.F := by
      rw [← f.derived_basis]
      apply (Subgroup.closure_le e.F).mpr
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      have huF : f.u ∈ e.F := by
        have hu : f.u ∈ E ⊓ e.F := by
          rw [← f.inf_basis]
          exact subset_closure (by simp)
        exact hu.2
      rcases hg with rfl | rfl | rfl | rfl | rfl
      · exact e.z_mem_inf.2
      · exact n.t_mem_inf.2
      · exact n.v_mem_inf.2
      · exact huF
      · exact hwF
    have hcard : Nat.card E = 32 := by
      rw [card_map_of_injective (K := commutator K) (f := embed)
        ((H).subtype_injective.comp K.subtype_injective)]
      exact (parrott_centralizer_structure z h).2.2.2.2.2.2.1
    exact e.ne_derived (eq_of_le_of_card_ge hEF (by rw [e.card, hcard])).symm
  rw [mem_zpowers_iff_mem_range_orderOf, h.involution] at hc
  obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hc
  have hi2 : i < 2 := Finset.mem_range.mp hi
  interval_cases i
  · exact (hne (by simpa using heq.symm)).elim
  · simpa using heq.symm

/-- The compatible three-generator selection through (8). No c or core
generation equality is assumed. -/
public structure ParrottSylowThreeGeneratorData (n : ParrottNormalizerFusionData e)
    extends ParrottSylowActionData n where
  a : G
  b : G
  d : G
  elementary_basis : closure ({z, n.t, n.v, u, a} : Set G) = e.F
  b_mem_core : b ∈ J
  d_mem_core : d ∈ J
  comm_bt : Commute b n.t
  d_sq : d ^ 2 = 1
  eq02_bw : Tits.parrottCommutator b w = 1
  eq02_aw : Tits.parrottCommutator a w = z
  eq02_bu : Tits.parrottCommutator b u = z
  eq03_db : Tits.parrottCommutator d b = n.v
  eq03_dt : Tits.parrottCommutator d n.t = z
  eq03_b : b ^ 2 = n.v
  eq05_ab : Tits.parrottCommutator a b = n.t
  eq07_dw : Tits.parrottCommutator d w = 1
  eq08_du : Tits.parrottCommutator d u = 1
  ax_alternative : Tits.parrottCommutator a x = 1 ∨ Tits.parrottCommutator a x = n.t

/-- Complete the initial frame after selecting c and proving core generation. -/
public def ParrottSylowThreeGeneratorData.toInitial
    (f : ParrottSylowThreeGeneratorData n) (c : G)
    (hcu : Tits.parrottCommutator c f.u = 1)
    (hcw : Tits.parrottCommutator c f.w = 1)
    (hct : Tits.parrottCommutator c n.t = 1)
    (hcv : Tits.parrottCommutator c n.v = z)
    (hgen : closure ({f.a, f.b, c, f.d} : Set G) = J) :
    ParrottSylowInitialData n where
  toParrottSylowActionData := f.toParrottSylowActionData
  a := f.a
  b := f.b
  c := c
  d := f.d
  elementary_basis := f.elementary_basis
  core_generators := hgen
  comm_bt := f.comm_bt
  d_sq := f.d_sq
  eq02_bw := f.eq02_bw
  eq02_aw := f.eq02_aw
  eq02_bu := f.eq02_bu
  eq03_db := f.eq03_db
  eq03_dt := f.eq03_dt
  eq03_b := f.eq03_b
  eq05_ab := f.eq05_ab
  eq07_dw := f.eq07_dw
  eq08_du := f.eq08_du
  eq09_cu := hcu
  eq09_cw := hcw
  eq10_ct := hct
  eq10_cv := hcv
  ax_alternative := f.ax_alternative

end Stellmacher.Recognition
