module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.LocalDichotomy.QuotientGap.Transfer
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.CoverFusion.Reduction

/-!
# Covering-center reduction and the cyclic-four obstruction

A center of order at most two is fixed by every automorphism. The two
exceptional elementary-four centers of 16.1.2(2) are excluded by the
commuting-conjugate equality and the involutory lifting clauses of I.2.2.
These exact earlier source outputs remain explicit inputs. The surviving
alternative retains both actual isomorphisms: L/Z(L) with M₂₂ and Z(L)
with the cyclic group of order four.

There is a genuine obstruction to simply dropping fixation from the
quotient-transfer argument. A nontrivial automorphism of a cyclic-four
center acts by inversion. If a fixed quotient involution lifts to an
involution y, its central displacement has square one. Taking a central
square root and multiplying y by it gives a fixed lift. Consequently, if
all quotient involutions lift, there is no missing involution at all.
This conditional obstruction does not refute the full ambient source
statement. Excluding its nonfixed cyclic-four branch is still required.

In particular, 16.4.7 excludes the Sz(2)/E₁₆ outer-action type, not all
M₂₂ covers. Neither that statement nor the source center alternative
alone excludes the remaining L₃(2)/E₈ type with cyclic-four center.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.2(2), printed p.1170; I.2.2(3b),(4),(6), pp.409–410 and its proof
on p.412; 16.4.7, pp.1186–1187; proof of 16.4.9(2), p.1190.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter16.Intersections.OuterReduction.LocalDichotomy.QuotientGap.CenterControl
variable {H : Type*} [Group H]

/-- Every automorphism fixes a center of order at most two pointwise. -/
theorem center_fixed_of_card_le_two [Finite H] (a : MulAut H)
    (hc : Nat.card (center H) ≤ 2) : center H ≤ a.fixedSubgroup := by
  intro x hx
  apply (MulAut.mem_fixedSubgroup _ _).mpr
  let e := centerCongr a
  have he : e (⟨x, hx⟩ : center H) = ⟨x, hx⟩ := by
    by_cases hc1 : Nat.card (center H) = 1
    · have := (Nat.card_eq_one_iff_unique.mp hc1).1
      exact Subsingleton.elim _ _
    · have hc2 : Nat.card (center H) = 2 := by have := Nat.card_pos (α := center H); omega
      by_cases hx1 : (⟨x, hx⟩ : center H) = 1
      · rw [hx1, map_one]
      · obtain ⟨w, _, hw⟩ := (Nat.card_eq_two_iff' (1 : center H)).mp hc2
        exact (hw _ (fun hh => hx1 (e.injective (hh.trans e.map_one.symm)))).trans
          (hw _ hx1).symm
  exact congrArg Subtype.val he

private theorem elementary_center_of_equiv
    (e : center H ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :
    ∀ c ∈ center H, c ^ 2 = 1 := by
  intro c hc
  have hh : ∀ v : Multiplicative (ZMod 2) × Multiplicative (ZMod 2), v ^ 2 = 1 := by decide
  have he : (⟨c, hc⟩ : center H) ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, map_one, hh]
  exact congrArg Subtype.val he

private theorem c4_inversion_of_ne_one (b : MulAut (Multiplicative (ZMod 4))) (hb : b ≠ 1) :
    ∀ x, b x = x⁻¹ := by
  let c : Multiplicative (ZMod 4) := Multiplicative.ofAdd 1
  have hc2 : c ^ 2 ≠ 1 := by decide
  have he : ∀ y : Multiplicative (ZMod 4), y ^ 2 ≠ 1 → y = c ∨ y = c⁻¹ := by decide
  have hall : ∀ x : Multiplicative (ZMod 4), x = 1 ∨ x = c ∨ x = c ^ 2 ∨ x = c ^ 3 := by decide
  have hbc : b c = c⁻¹ := by
    rcases he (b c) (fun h => hc2 (b.injective (by simpa only [map_pow, map_one] using h))) with h | h
    · exfalso
      apply hb
      ext x
      rcases hall x with rfl | rfl | rfl | rfl <;> simp [h]
    · exact h
  intro x
  rcases hall x with rfl | rfl | rfl | rfl <;> simp [hbc, inv_pow]

private theorem center_inversion_of_nonfixed_cyclic_four
    (N : Subgroup H) [N.Characteristic]
    (e : N ≃* Multiplicative (ZMod 4)) (a : MulAut H)
    (hn : ¬ N ≤ a.fixedSubgroup) : ∀ c ∈ N, a c = c⁻¹ := by
  let b : MulAut (Multiplicative (ZMod 4)) := MulAut.congr e (MulAut.characteristic N a)
  have hb : b ≠ 1 := by
    intro hb
    apply hn
    intro c hc
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    have hh := DFunLike.congr_fun hb (e ⟨c, hc⟩)
    change e (MulAut.characteristic N a (e.symm (e ⟨c, hc⟩))) = e ⟨c, hc⟩ at hh
    rw [e.symm_apply_apply] at hh
    exact congrArg Subtype.val (e.injective hh)
  intro c hc
  have hh := c4_inversion_of_ne_one b hb (e ⟨c, hc⟩)
  change e (MulAut.characteristic N a (e.symm (e ⟨c, hc⟩))) = (e ⟨c, hc⟩)⁻¹ at hh
  rw [e.symm_apply_apply, ← map_inv] at hh
  exact congrArg Subtype.val (e.injective hh)

/-- If an involution lifts, inversion on a cyclic-four kernel allows a fixed lift. -/
private theorem fixed_involution_mem_image_of_nonfixed_cyclic_four
    (N : Subgroup H) [N.Characteristic]
    (e : N ≃* Multiplicative (ZMod 4)) (a : MulAut H)
    (hn : ¬ N ≤ a.fixedSubgroup) (hcentral : N ≤ center H)
    (v : H ⧸ N) (hv : (N).quotientAut a v = v)
    (hlift : ∃ y : H, QuotientGroup.mk' (N) y = v ∧ y ^ 2 = 1) :
    v ∈ a.fixedSubgroup.map (QuotientGroup.mk' (N)) := by
  obtain ⟨y, rfl, hy2⟩ := hlift
  rw [quotientAut_apply_mk] at hv
  let d := a y * y⁻¹
  have hd : d ∈ N := by
    change a y * y⁻¹ ∈ N
    simpa only [div_eq_mul_inv] using
      (QuotientGroup.eq_iff_div_mem (N := N) (x := a y) (y := y)).mp hv
  have hdcy : Commute d y := (mem_center_iff.mp (hcentral hd) y).symm
  have hd2 : d ^ 2 = 1 := by
    have hh := hdcy.mul_pow 2
    rw [show d * y = a y by simp [d], ← map_pow, hy2, map_one, mul_one] at hh
    exact hh.symm
  have hroots : ∀ d : Multiplicative (ZMod 4), d ^ 2 = 1 → ∃ c, c ^ 2 = d := by decide
  have he2 : (e ⟨d, hd⟩) ^ 2 = 1 := by
    rw [← map_pow, ← e.map_one]
    exact congrArg e (show (⟨d, hd⟩ : N) ^ 2 = 1 from Subtype.ext hd2)
  obtain ⟨c0, hc0⟩ := hroots (e ⟨d, hd⟩) he2
  let c : N := e.symm c0
  have hc : (c : H) ^ 2 = d := by
    apply_fun e.symm at hc0
    rw [map_pow, e.symm_apply_apply] at hc0
    exact congrArg Subtype.val hc0
  have hac : a (c : H) = (c : H)⁻¹ := center_inversion_of_nonfixed_cyclic_four N e a hn c c.property
  have hay : a y = d * y := by simp [d]
  have hfixed : a (y * c) = y * c := by
    rw [map_mul, hac, hay, ← hc]
    have hcomm : Commute y (c : H) := mem_center_iff.mp (hcentral c.property) y
    calc
      (c : H) ^ 2 * y * (c : H)⁻¹ = y * ((c : H) ^ 2 * (c : H)⁻¹) := by
        rw [← (hcomm.pow_right 2).eq, mul_assoc]
      _ = y * c := by group
  refine ⟨y * c, (MulAut.mem_fixedSubgroup _ _).mpr hfixed, ?_⟩
  have hqc : QuotientGroup.mk' N (c : H) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr c.property
  rw [map_mul, hqc, mul_one]

open CFSG.Quasithin CFSG.Quasithin.Chapter16
open Intersections Intersections.OuterReduction
open LocalDichotomy LocalDichotomy.QuotientGap ComponentTransfer.Intrinsic
variable {G : Type*} [Group G] [Finite G] {𝒦 : GroupClass}
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

omit [Finite G] in
private theorem involution_lifting_core (hc : center L = pCore 2 L)
    (hlift : ∀ v : L ⧸ center L, orderOf v = 2 →
      ∃ y : L, QuotientGroup.mk' (center L) y = v ∧ orderOf y = 2) :
    ∀ v : L ⧸ pCore 2 L, orderOf v = 2 →
      ∃ y : L, QuotientGroup.mk' (pCore 2 L) y = v ∧ y ^ 2 = 1 := by
  let e := QuotientGroup.quotientMulEquivOfEq hc
  intro v hv
  obtain ⟨y, hy, hy2⟩ := hlift (e.symm v) ((e.symm.orderOf_eq v).trans hv)
  refine ⟨y, ?_, hy2 ▸ pow_orderOf_eq_one y⟩
  have hh := congrArg e hy
  change e (QuotientGroup.mk' (center L) y) = e (e.symm v) at hh
  rw [e.apply_symm_apply] at hh
  exact (QuotientGroup.quotientMulEquivOfEq_mk hc y).symm.trans hh

/-- The two exceptional elementary-four centers are handled using the actual
involution-lifting clauses of I.2.2(3b),(4). No center action is assumed. -/
theorem false_of_elementary_four_center
    (hG : Hypothesis1611 𝒦 G) (h : IntersectionSetup T z L g R)
    (hr2 : orderOf r = 2) (hn : r ∈ normalizer (L : Set G)) (hzL : z ∈ L)
    (hgeom : {s : G | (∃ l ∈ L, MulAut.conj l r = s) ∧ Commute r s} = {r, r * z})
    (hfour : Nonempty (center L ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))))
    (hlift : ∀ v : L ⧸ center L, orderOf v = 2 →
      ∃ y : L, QuotientGroup.mk' (center L) y = v ∧ orderOf y = 2)
    (q : L ⧸ pCore 2 L) (hq2 : orderOf (quotientAction hn q * q⁻¹) = 2) : False := by
  obtain ⟨e⟩ := hfour
  apply false_of_elementary_center_and_involution_lifting hG h hr2 hn hzL hgeom
    (elementary_center_of_equiv e) ?_ q hq2
  exact involution_lifting_core
    (hG.evenType.component_center_eq_twoCore h.involution h.component) hlift

/-- The exact 16.1.2(2) alternative and the elementary-center lifting clauses
reduce center fixation to the cyclic-four M₂₂ cover. This is a reduction,
not a proof that the remaining cover is absent from the ambient setup. -/
theorem center_fixed_or_m22_cyclic_four
    (hG : Hypothesis1611 𝒦 G) (h : IntersectionSetup T z L g R)
    (hr2 : orderOf r = 2) (hn : r ∈ normalizer (L : Set G)) (hzL : z ∈ L)
    (hgeom : {s : G | (∃ l ∈ L, MulAut.conj l r = s) ∧ Commute r s} = {r, r * z})
    (hcent : CoverFusion.SourceCenterAlternative L)
    (hlift : (Nonempty ((L ⧸ center L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1) ∨
        ClassicalGroup.IsPSL (L ⧸ center L) 3 4) →
      Nonempty (center L ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) →
      ∀ v : L ⧸ center L, orderOf v = 2 →
        ∃ y : L, QuotientGroup.mk' (center L) y = v ∧ orderOf y = 2)
    (q : L ⧸ pCore 2 L) (hq2 : orderOf (quotientAction hn q * q⁻¹) = 2) :
    center L ≤ (action hn).fixedSubgroup ∨
      (Nonempty ((L ⧸ center L) ≃* Sporadic.Mathieu.M22) ∧
        Nonempty (center L ≃* Multiplicative (ZMod 4))) := by
  rcases hcent with hc | ⟨hmodel, hc⟩ | hc
  · exact Or.inl (center_fixed_of_card_le_two (action hn) hc)
  · exact (false_of_elementary_four_center hG h hr2 hn hzL hgeom hc
      (hlift hmodel hc) q hq2).elim
  · exact Or.inr hc

/-- Obstruction to extending the fixed-center transfer to a nonfixed cyclic-four
center: if quotient involutions lift involutively, every fixed quotient
involution is in the centralizer image. Thus this branch must be excluded
using additional ambient information before asserting the requested gap.
The lifting assertion remains explicit; no cover model is assumed split. -/
theorem no_missing_involution_of_nonfixed_cyclic_four
    (hG : Hypothesis1611 𝒦 G) (h : IntersectionSetup T z L g R)
    (hn : r ∈ normalizer (L : Set G))
    (hfour : Nonempty (center L ≃* Multiplicative (ZMod 4)))
    (hnonfix : ¬ center L ≤ (action hn).fixedSubgroup)
    (hlift : ∀ v : L ⧸ center L, orderOf v = 2 →
      ∃ y : L, QuotientGroup.mk' (center L) y = v ∧ orderOf y = 2) :
    ¬ ∃ v : quotientFixed hn, orderOf v = 2 ∧ v ∉ imageInFixed hn := by
  obtain ⟨e⟩ := hfour
  have hc := hG.evenType.component_center_eq_twoCore h.involution h.component
  let ecore : pCore 2 L ≃* Multiplicative (ZMod 4) :=
    (MulEquiv.subgroupCongr hc.symm).trans e
  have hncore : ¬ pCore 2 L ≤ (action hn).fixedSubgroup := by rwa [← hc]
  have hliftcore : ∀ v : L ⧸ pCore 2 L, orderOf v = 2 →
      ∃ y : L, QuotientGroup.mk' (pCore 2 L) y = v ∧ y ^ 2 = 1 :=
    involution_lifting_core hc hlift
  rintro ⟨v, hv2, hvout⟩
  apply hvout
  exact fixed_involution_mem_image_of_nonfixed_cyclic_four (pCore 2 L) ecore (action hn)
    hncore hc.symm.le v ((MulAut.mem_fixedSubgroup _ _).mp v.property)
    (hliftcore v ((orderOf_coe v).trans hv2))
end CFSG.Quasithin.Chapter16.Intersections.OuterReduction.LocalDichotomy.QuotientGap.CenterControl
