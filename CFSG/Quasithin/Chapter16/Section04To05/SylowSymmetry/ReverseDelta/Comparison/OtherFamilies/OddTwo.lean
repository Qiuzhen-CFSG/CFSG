module
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.InnerOnly
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.OddLinear

/-!
# Fermat–Mersenne PSL₂ in the residual comparison

The proved inner row is a Sylow two-subgroup, so its two-residual is trivial.
Containment makes the outer two-residual trivial as well. Its fixed subgroup
would therefore be a two-group, contradicting the actual dihedral outer row.

`OddTwoTables` retains the large-prime source row and the small parameters
five and seven separately. Those two overlaps have S₃ fixed subgroups. The
inner calculation already handles both, without assuming p > 7. The outer
rows are explicit earlier table inputs; this module proves their comparison.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 16.1.5(2),
printed p.1171, its PSL₂(5) and PSL₂(7) overlaps with 16.1.4, and the proof
of 16.4.11(2), printed p.1193. Residuals here mean O², not O₂.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

private theorem fixed_twoGroup_of_residual_bot {H : Type*} [Group H] [Finite H]
    (h : pResidual 2 H = ⊥) : IsPGroup 2 H := by
  have hi : Function.Injective (QuotientGroup.mk' (pResidual 2 H)) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rwa [QuotientGroup.ker_mk']
  exact (isPGroup_quotient_pResidual 2).of_injective _ hi

/-- In the contrary configuration a two-group inner centralizer forces a
 two-group outer centralizer. Both groups here are upstairs in L and L′. -/
theorem outer_fixed_twoGroup_of_inner (d : Contrary T z L g R r)
    (hin : IsPGroup 2 (action (d.setup.sylow_normalizes
      (d.setup.le_sylow d.mem))).fixedSubgroup) :
    IsPGroup 2 (action d.z_normalizes).fixedSubgroup := by
  have hC : IsPGroup 2 (L ⊓ centralizer ({r} : Set G) : Subgroup G) :=
    hin.of_equiv (fixedCentralizerEquiv _)
  have hP : pResidual 2 (L ⊓ centralizer ({r} : Set G) : Subgroup G) = ⊥ := by
    apply le_bot_iff.mp
    exact sInf_le ⟨inferInstance, hC.to_quotient ⊥⟩
  have hres : residual L r = ⊥ := by
    change (pResidual 2 (L ⊓ centralizer ({r} : Set G) : Subgroup G)).map _ = ⊥
    rw [hP, Subgroup.map_bot]
  have hout : residual (L.conjBy g) z = ⊥ :=
    le_bot_iff.mp (hres ▸ d.residual_normal.1)
  have hfixed : pResidual 2 (action d.z_normalizes).fixedSubgroup = ⊥ := by
    have hh := residual_subgroupOf_eq d.z_normalizes
    rw [hout, bot_subgroupOf] at hh
    exact (map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp hh.symm
  exact fixed_twoGroup_of_residual_bot hfixed

/-- Lean's DihedralGroup n has order 2n. This is D_(p+ε) in 16.1.5(2). -/
def PSLTwoOuterRow {F : Type} [Field F] (p : ℕ) (a : MulAut PSL(2,F)) : Prop :=
  ∃ n : ℕ, 2 * n = (if p % 4 = 1 then p + 1 else p - 1) ∧
    Nonempty (a.fixedSubgroup ≃* DihedralGroup n)

private theorem not_twoGroup_dihedral {n : ℕ} (hn : Odd n) (hn1 : 1 < n) :
    ¬ IsPGroup 2 (DihedralGroup n) := by
  intro h
  have hx : (DihedralGroup.r 1 : DihedralGroup n) ≠ 1 := by
    intro he
    have hh := DihedralGroup.orderOf_r_one (n := n)
    rw [he, orderOf_one] at hh
    omega
  have hd := h.dvd_orderOf hx
  rw [DihedralGroup.orderOf_r_one] at hd
  exact (Nat.not_even_iff_odd.mpr hn) (even_iff_two_dvd.mpr hd)

/-- The exact outer row is not a two-group, including p = 5 and p = 7. -/
theorem PSLTwoOuterRow.not_twoGroup {F : Type} [Field F] {p : ℕ}
    {a : MulAut PSL(2,F)} (h : PSLTwoOuterRow p a) (hp : Odd p) (hp5 : 5 ≤ p) :
    ¬ IsPGroup 2 a.fixedSubgroup := by
  obtain ⟨n, hn, ⟨e⟩⟩ := h
  have hpmod : p % 2 = 1 := Nat.odd_iff.mp hp
  have hnodd : Odd n := by
    apply Nat.odd_iff.mpr
    split at hn <;> omega
  have hn1 : 1 < n := by split at hn <;> omega
  exact fun htwo => not_twoGroup_dihedral hnodd hn1 (htwo.of_equiv e)

/-- The inner row already proved in OddLinear excludes every prime parameter
 as soon as its actual outer fixed-subgroup row is supplied. -/
theorem not_pslTwo_of_outer_table (d : Contrary T z L g R r)
    {F : Type} [Field F] [Finite F] {p : ℕ}
    (hF : Nat.card F = p) (hp : IsFermatOrMersennePrime p)
    (e : L ≃* PSL(2,F))
    (table : ∀ a : MulAut PSL(2,F), orderOf a = 2 →
      (¬ ∃ x, a = MulAut.conj x) → PSLTwoOuterRow p a) : False := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  have hL : ClassicalGroup.IsPSL L 2 p := ⟨F, inferInstance, inferInstance, hF, ⟨e⟩⟩
  have hp5 := OtherPreliminaries.OddLinear.pslTwo_parameter_ge_five hp hL
  let ai := action (d.setup.sylow_normalizes (d.setup.le_sylow d.mem))
  let a := MulAut.congr e ai
  have ha : orderOf a = 2 := ((MulAut.congr e).orderOf_eq ai).trans d.inner_action_order
  have hia : ∃ x, a = MulAut.conj x := (MulAut.congr_inner_iff e ai).mpr d.inner_action
  obtain ⟨S, hS⟩ := OtherPreliminaries.OddLinear.pslTwo_inner_involution hF hp hp5 a ha hia
  have hin : IsPGroup 2 ai.fixedSubgroup :=
    (hS ▸ S.isPGroup').of_equiv (MulAut.fixedSubgroupCongr e ai).symm
  let ec : L ≃* L.conjBy g := (MulAut.conj g).subgroupMap L
  let eM := ec.symm.trans e
  let b := MulAut.congr eM (action d.z_normalizes)
  have hb : orderOf b = 2 :=
    ((MulAut.congr eM).orderOf_eq _).trans d.outer_action_order
  have hob : ¬ ∃ x, b = MulAut.conj x := fun h =>
    d.outer_action ((MulAut.congr_inner_iff eM _).mp h)
  exact (table b hb hob).not_twoGroup (hp.1.odd_of_ne_two (by omega)) hp5
    ((outer_fixed_twoGroup_of_inner d hin).of_equiv (MulAut.fixedSubgroupCongr eM _))

/-- The large-prime source row and its two small overlaps are separate inputs.
The small rows are the S₃ centralizers in PGL₂(5) and PGL₂(7), expressed
as actual dihedral-group isomorphisms. No parameter bound is suppressed. -/
structure OddTwoTables : Prop where
  large : ∀ (F : Type) [Field F] [Finite F] (p : ℕ), Nat.card F = p →
    IsFermatOrMersennePrime p → 7 < p → ∀ a : MulAut PSL(2,F), orderOf a = 2 →
      (¬ ∃ x, a = MulAut.conj x) → PSLTwoOuterRow p a
  small : ∀ (F : Type) [Field F] [Finite F],
    (Nat.card F = 5 ∨ Nat.card F = 7) → ∀ a : MulAut PSL(2,F), orderOf a = 2 →
      (¬ ∃ x, a = MulAut.conj x) → Nonempty (a.fixedSubgroup ≃* DihedralGroup 3)

/-- Eliminate the complete Fermat–Mersenne alternative of (E2)(ii),
 explicitly retaining the two small-prime overlaps in the table contract. -/
theorem not_pslTwo_family (d : Contrary T z L g R r) (tables : OddTwoTables)
    (h : ∃ p, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL L 2 p) : False := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  obtain ⟨p, hp, hL⟩ := h
  have hp5 := OtherPreliminaries.OddLinear.pslTwo_parameter_ge_five hp hL
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hL
  apply not_pslTwo_of_outer_table d hF hp e
  intro a ha hoa
  by_cases hlarge : 7 < p
  · exact tables.large F p hF hp hlarge a ha hoa
  · have hpodd := hp.1.odd_of_ne_two (by omega)
    have hpmod := Nat.odd_iff.mp hpodd
    have hsmall : p = 5 ∨ p = 7 := by omega
    refine ⟨3, ?_, tables.small F (hF ▸ hsmall) a ha hoa⟩
    rcases hsmall with rfl | rfl <;> norm_num
end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies
