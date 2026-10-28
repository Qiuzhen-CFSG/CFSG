module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.RootProduct
public import Theory.Frattini.BinarySquares

/-!
# The elementary quotient of the canonical root product

Both core intersections are normal in their join. Their cross commutators
therefore lie in their intersection E. Squares in the original and conjugate
cores lie in the two respective central involution lines, both contained in E.
The literal product formula now puts every square of R in E. Consequently the
actual quotient R/E is elementary abelian of order sixteen. In each core
centralizer a quaternion square supplies its central involution; together
these show that the Frattini subgroup of R is exactly E.

These are unconditional inputs to the normalizer action calculation, not a
recognition of that action or a claim that E is already the full center of R.
Source: Aschbacher, *Sporadic Groups* (1994), 8.15(2–3) and 46.2–46.3,
printed pp.29–30 and 251.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.ReturningPair

variable {G : Type*} [Group G] [Finite G] {D : Seed G} (P : ReturningPair D)

theorem R_le_normalizer_leftCore : P.R ≤ normalizer (P.leftCore : Set G) := by
  apply le_trans _ inf_normalizer_le_normalizer_inf
  apply le_inf
  · rw [D.localType.normalizer_core]
    exact P.R_le_double_centralizer.trans inf_le_left
  · exact (P.R_le_double_centralizer.trans inf_le_right).trans le_normalizer

theorem R_le_normalizer_rightCore : P.R ≤ normalizer (P.rightCore : Set G) := by
  apply le_trans _ inf_normalizer_le_normalizer_inf
  apply le_inf
  · rw [P.normalizer_conjugateCore]
    exact P.R_le_double_centralizer.trans inf_le_right
  · exact (P.R_le_double_centralizer.trans inf_le_left).trans le_normalizer

/-- Cross commutators of the two literal factors lie in the marked four-group. -/
theorem cross_commutator_le_E (L : LocalCensus D) :
    ⁅P.leftCore, P.rightCore⁆ ≤ P.E := by
  rw [← P.leftCore_inf_rightCore L]
  exact le_inf
    (le_normalizer_iff_commutator_le_left.mp
      ((le_sup_right : P.rightCore ≤ P.R).trans P.R_le_normalizer_leftCore))
    (le_normalizer_iff_commutator_le_right.mp
      ((le_sup_left : P.leftCore ≤ P.R).trans P.R_le_normalizer_rightCore))

private theorem core_square_mem_line {x : G} (hx : x ∈ ambientCore D.z) :
    x ^ 2 ∈ zpowers D.z := by
  let Q := ambientCore D.z
  let q : Q := ⟨x, hx⟩
  let := D.localType.ambientCore_isExtraspecial
  let := IsExtraspecial.quotient_elementary_abelian 2 Q
  have hs : q ^ 2 ∈ center Q := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (Q ⧸ center Q)) _
  have hm := mem_map_of_mem Q.subtype hs
  rwa [D.localType.core_center_image] at hm

theorem leftCore_square_mem_E {x : G} (hx : x ∈ P.leftCore) : x ^ 2 ∈ P.E :=
  (le_sup_left : zpowers D.z ≤ P.E) (core_square_mem_line hx.1)

theorem rightCore_square_mem_E {x : G} (hx : x ∈ P.rightCore) : x ^ 2 ∈ P.E := by
  obtain ⟨q, hq, rfl⟩ := hx.1
  have hq2 := core_square_mem_line hq
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hq2
  apply (le_sup_right : zpowers P.u ≤ P.E)
  exact mem_zpowers_iff.mpr ⟨n, by
    simpa only [map_pow, map_zpow, u, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      using congrArg (MulAut.conj P.g) hn⟩

theorem E_subgroupOf_le_center : P.E.subgroupOf P.R ≤ center P.R := by
  intro x hx
  obtain ⟨y, hy, he⟩ := P.E_le_center_image hx
  have hxy : y = x := Subtype.ext he
  exact hxy ▸ hy

instance E_subgroupOf_normal : (P.E.subgroupOf P.R).Normal where
  conj_mem x hx g := by
    have he := mem_center_iff.mp (P.E_subgroupOf_le_center hx) g
    simpa only [he, mul_inv_cancel_right] using hx

/-- Squares of the actual product, not just of either core, lie in E. -/
theorem R_square_mem_E (L : LocalCensus D) {x : G} (hx : x ∈ P.R) :
    x ^ 2 ∈ P.E := by
  change x ∈ (P.R : Set G) at hx
  rw [P.R_coe] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  have hc : ⁅b, a⁆ ∈ P.E := by
    have hcross := P.cross_commutator_le_E L
    rw [commutator_comm] at hcross
    exact hcross (commutator_mem_commutator hb ha)
  have haR : a ∈ P.R := (le_sup_left : P.leftCore ≤ P.R) ha
  have hcentral := mem_center_iff.mp
    (P.E_subgroupOf_le_center (show (⟨⁅b, a⁆, P.E_le_R hc⟩ : P.R) ∈
      P.E.subgroupOf P.R from hc)) (⟨a, haR⟩ : P.R)
  have he : a * ⁅b, a⁆ * a⁻¹ = ⁅b, a⁆ :=
    mul_inv_eq_iff_eq_mul.mpr (congrArg Subtype.val hcentral)
  have hid : (a * b) ^ 2 = (a * ⁅b, a⁆ * a⁻¹) * a ^ 2 * b ^ 2 := by
    simp [commutatorElement_def, pow_two, mul_assoc]
  rw [hid, he]
  exact P.E.mul_mem (P.E.mul_mem hc (P.leftCore_square_mem_E ha))
    (P.rightCore_square_mem_E hb)

/-- The literal R/E from source 8.15 is elementary abelian. -/
theorem root_quotient_elementary (L : LocalCensus D) :
    IsElementaryAbelian 2 (P.R ⧸ P.E.subgroupOf P.R) := by
  have hp (x : P.R ⧸ P.E.subgroupOf P.R) : x ^ 2 = 1 := by
    induction x using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact P.R_square_mem_E L x.property
  have hi (x : P.R ⧸ P.E.subgroupOf P.R) : x⁻¹ = x :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hp x)
  exact {
    toIsMulCommutative := isMulCommutative_iff.mpr fun a b => by
      calc
        a * b = (a * b)⁻¹ := (hi _).symm
        _ = b⁻¹ * a⁻¹ := mul_inv_rev _ _
        _ = b * a := by rw [hi, hi]
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp }

theorem root_quotient_card (L : LocalCensus D) :
    Nat.card (P.R ⧸ P.E.subgroupOf P.R) = 16 := by
  have h := card_eq_card_quotient_mul_card_subgroup (P.E.subgroupOf P.R)
  have he : Nat.card (P.E.subgroupOf P.R) = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe P.E_le_R).toEquiv).trans P.E_card
  rw [P.R_card L, he] at h
  omega

/-- This source quotient kills the actual Frattini subgroup of R. -/
theorem frattini_image_le_E (L : LocalCensus D) :
    (frattini P.R).map P.R.subtype ≤ P.E := by
  rw [(P.R_isPGroup L).frattini_eq_closure_squares, map_le_iff_le_comap]
  apply (closure_le _).mpr
  rintro _ ⟨x, rfl⟩
  exact P.R_square_mem_E L x.property

private theorem model_square_witness : ∀ v : MinusExtraspecial.Model,
    ∃ a : MinusExtraspecial.Model, a * v = v * a ∧
      a ^ 2 = MinusExtraspecial.quaternion MinusExtraspecial.z := by
  decide +kernel

private theorem core_square_witness (v : ambientCore D.z) :
    ∃ a : ambientCore D.z, a * v = v * a ∧ (a : G) ^ 2 = D.z := by
  let e : ambientCore D.z ≃* MinusExtraspecial.Model :=
    ((localCore D.z).equivMapOfInjective (involutionCentralizer D.z).subtype
      (involutionCentralizer D.z).subtype_injective).symm.trans D.localType.core_equiv.some
  let c : ambientCore D.z := ⟨D.z, HTypeAt.involution_mem_core⟩
  have hc1 : c ≠ 1 := by
    intro hc
    have hz : D.z = 1 := congrArg Subtype.val hc
    have ho := D.localType.involution
    simp [hz] at ho
  have hce : e c ∈ center MinusExtraspecial.Model := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← e.map_mul, ← e.map_mul]
    exact congrArg e (Subtype.ext
      (mem_centralizer_singleton_iff.mp (ambientCore_le D.z x.property)))
  have hec : e c = MinusExtraspecial.quaternion MinusExtraspecial.z :=
    ((MinusExtraspecial.mem_center_iff _).mp hce).resolve_left
      (fun h => hc1 (e.injective (h.trans e.map_one.symm)))
  obtain ⟨a, ha, hs⟩ := model_square_witness (e v)
  refine ⟨e.symm a, e.injective ?_, ?_⟩
  · simpa only [map_mul, e.apply_symm_apply] using ha
  · have he : (e.symm a) ^ 2 = c := by
      apply e.injective
      simpa only [map_pow, e.apply_symm_apply, hec] using hs
    exact congrArg (fun a : ambientCore D.z => (a : G)) he

/-- The original central involution is a square in the first literal factor. -/
theorem z_square_in_leftCore : ∃ a ∈ P.leftCore, a ^ 2 = D.z := by
  obtain ⟨a, ha, hs⟩ := core_square_witness (⟨P.u, P.mem_core⟩ : ambientCore D.z)
  exact ⟨a, ⟨a.property, mem_centralizer_singleton_iff.mpr
    (congrArg (fun a : ambientCore D.z => (a : G)) ha)⟩, hs⟩

/-- The conjugate central involution is a square in the second literal factor. -/
theorem u_square_in_rightCore (L : LocalCensus D) :
    ∃ a ∈ P.rightCore, a ^ 2 = P.u := by
  obtain ⟨q, hq, hqz⟩ := P.z_mem_conjugateCore L
  obtain ⟨a, ha, hs⟩ := core_square_witness (⟨q, hq⟩ : ambientCore D.z)
  let e := MulAut.conj P.g
  refine ⟨e a, ⟨mem_map_of_mem e.toMonoidHom a.property, ?_⟩, ?_⟩
  · apply mem_centralizer_singleton_iff.mpr
    have hm := congrArg e (congrArg (fun a : ambientCore D.z => (a : G)) ha)
    simpa only [Subgroup.coe_mul, map_mul, show e q = D.z from hqz] using hm
  · simpa only [map_pow, e, u, MulAut.conj_apply] using congrArg e hs

/-- The intrinsic Frattini subgroup has exactly the source four-group as image. -/
theorem frattini_image_eq_E (L : LocalCensus D) :
    (frattini P.R).map P.R.subtype = P.E := by
  apply le_antisymm (P.frattini_image_le_E L)
  have hs (a : G) (ha : a ∈ P.R) :
      a ^ 2 ∈ (frattini P.R).map P.R.subtype := by
    refine mem_map.mpr ⟨(⟨a, ha⟩ : P.R) ^ 2, ?_, by simp⟩
    rw [(P.R_isPGroup L).frattini_eq_closure_squares]
    exact subset_closure ⟨⟨a, ha⟩, rfl⟩
  apply sup_le <;> apply zpowers_le.mpr
  · obtain ⟨a, ha, he⟩ := P.z_square_in_leftCore
    exact he ▸ hs a ((le_sup_left : P.leftCore ≤ P.R) ha)
  · obtain ⟨a, ha, he⟩ := P.u_square_in_rightCore L
    exact he ▸ hs a ((le_sup_right : P.rightCore ≤ P.R) ha)

/-- The full normalizer preserves E before any action or center recognition. -/
theorem normalizer_R_le_normalizer_E (L : LocalCensus D) :
    normalizer (P.R : Set G) ≤ normalizer (P.E : Set G) := by
  rw [← P.frattini_image_eq_E L]
  exact normalizer_le_normalizer_characteristic_image P.R (frattini P.R)

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.ReturningPair
