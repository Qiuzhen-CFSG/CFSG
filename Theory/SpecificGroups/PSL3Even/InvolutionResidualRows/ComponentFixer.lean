module
public import Theory.GroupAction.CommutingFixedComponentFixer
public import Theory.SpecificGroups.PSL3.FieldComponentFixer
public import Theory.SpecificGroups.PSL3Even.InvolutionResidualRows.Cases
public import Theory.SpecificGroups.PSL3Even.NonbinaryCentralizer.FixedGeneration
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.CComponent.QuasisimpleFactors

/-!
# Pointwise fixers of the binary linear-three field component

The field fixed group is simple, so its ordinary component is the whole fixed group. Conjugate the actual field row to coefficient Frobenius. The root-subfield pointwise-fixer theorem leaves precisely the identity and the field involution.

Source: Aschbacher–Smith 2.5.19, printed pp.560–563.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3.OuterSolvable
namespace Matrix.PSL3Even.InvolutionResidualRows
variable {F : Type*} [Field F] [Finite F]

theorem field_case_component_eq_top {n : ℕ} (a : MulAut PSL(3,F))
    (hf : FieldCase n a) (B : Subgroup a.fixedSubgroup)
    (hB : IsComponent a.fixedSubgroup B) : B = ⊤ := by
  obtain ⟨g, σ, hσ, he, hs, ⟨c, hc⟩, _⟩ := hf
  have hcj : IsConj a (fieldAction F σ) := isConj_iff.mpr ⟨linearConj F c, hc⟩
  have hh := NonbinaryCentralizer.field_fixed_simple_perfect_of_isConj σ hs a hcj
  rcases hB.1.eq_bot_or_top_of_isSimpleGroup hh.1 with hb | ht
  · have hz : Group.IsSolvable B := by rw [hb]; infer_instance
    exact (hB.isCComponent.not_isSolvable hz).elim
  · exact ht

theorem field_case_component_fixer_eq_one_or {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2 ^ n) (a : MulAut PSL(3,F))
    (hf : FieldCase n a) (B : Subgroup a.fixedSubgroup)
    (hB : IsComponent a.fixedSubgroup B) (b : MulAut PSL(3,F))
    (hb : ∀ x : B, b ((x : a.fixedSubgroup) : PSL(3,F)) = x) :
    b = 1 ∨ b = a := by
  classical
  have hBtop := field_case_component_eq_top a hf B hB
  have hbfix (x : a.fixedSubgroup) : b (x : PSL(3,F)) = x :=
    hb ⟨x, by rw [hBtop]; trivial⟩
  obtain ⟨g, σ, hσ, he, hs, ⟨c, hc⟩, _⟩ := hf
  let u := linearConj F c
  let d := MulAut.congr u b
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hroots : PSL3.FieldComponentFixer.fieldRoots σ ≤ (fieldAction F σ).fixedSubgroup := by
    apply (closure_le _).mpr
    rintro _ ⟨i,j,hij,x,hx,rfl⟩
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    rw [PSL3.FieldComponentFixer.fieldAction_rootElement, hx]
  have hdfix : d ∈ fixingSubgroup (MulAut PSL(3,F))
      (PSL3.FieldComponentFixer.fieldRoots σ : Set PSL(3,F)) := by
    intro x
    have hx : x.val ∈ (MulAut.congr u a).fixedSubgroup := by
      rw [show MulAut.congr u a = fieldAction F σ from hc]
      exact hroots x.property
    let y : a.fixedSubgroup := ⟨u.symm x.val, by
      apply (MulAut.mem_fixedSubgroup a _).mpr
      apply u.injective
      have he : u (a (u.symm x.val)) = x.val :=
        (MulAut.mem_fixedSubgroup (MulAut.congr u a) x.val).mp hx
      exact he.trans (u.apply_symm_apply x.val).symm⟩
    change u (b (u.symm x.val)) = x.val
    have hy : b (u.symm x.val) = u.symm x.val := hbfix y
    rw [hy, u.apply_symm_apply]
  have hmem : d ∈ (zpowers σ).map (fieldAction F) := by
    rw [← PSL3.FieldComponentFixer.standard_fixer_eq σ]
    refine ⟨?_, hdfix⟩
    rw [standard_eq_top_of_two_power_card F hn hF]
    trivial
  rw [MonoidHom.map_zpowers] at hmem
  have hpow : (fieldAction F σ) ^ 2 = 1 := by rw [← map_pow, hs, map_one]
  have hfin : IsOfFinOrder (fieldAction F σ) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, hpow⟩
  obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp (hfin.mem_zpowers_iff_mem_range_orderOf.mp hmem)
  have hk2 : k < 2 := (Finset.mem_range.mp hk).trans_le
    (orderOf_le_of_pow_eq_one (by decide : 0 < 2) hpow)
  interval_cases k
  · left
    apply (MulAut.congr u).injective
    simpa only [pow_zero, map_one] using heq.symm
  · right
    apply (MulAut.congr u).injective
    rw [show MulAut.congr u a = fieldAction F σ from hc]
    simpa only [pow_one] using heq.symm
theorem field_case_commuting_component_fixer_card_le_two {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2 ^ n) (a : MulAut PSL(3,F)) (ha : orderOf a = 2)
    (hf : FieldCase n a) (B : Subgroup a.fixedSubgroup)
    (hB : IsComponent a.fixedSubgroup B) :
    Nat.card (MulAut.commutingFixedComponentFixer a B) ≤ 2 := by
  have hle : MulAut.commutingFixedComponentFixer a B ≤ zpowers a := by
    intro b hb
    have hfix (x : B) : b ((x : a.fixedSubgroup) : PSL(3,F)) = x :=
      hb.2 ⟨((x : a.fixedSubgroup) : PSL(3,F)),
        mem_map_of_mem a.fixedSubgroup.subtype x.property⟩
    rcases field_case_component_fixer_eq_one_or hn hF a hf B hB b hfix with he | he
    · rw [he]; exact one_mem _
    · rw [he]; exact mem_zpowers a
  have hc := card_le_of_le hle
  rwa [Nat.card_zpowers,ha] at hc

end Matrix.PSL3Even.InvolutionResidualRows
