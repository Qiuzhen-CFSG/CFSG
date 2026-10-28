module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.Actions
public import Theory.GroupAction.SubgroupQuotientFullAction

/-!
# The actual quotient actions for Section 15.3

Conjugation by H descends to A/(Z ∩ A) when H normalizes both layers.
The representative formula identifies its kernel with C_H(A/Z), computed
inside H/Z. This connects faithfulness assertions to a homomorphism into
the automorphism group of the actual quotient, with relative normality.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.48–49, pp.1141–1143.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup

/-- Conjugation on the literal subgroup quotient A/(Z ∩ A). -/
noncomputable def quotientAction {G : Type*} [Group G] (H A Z : Subgroup G)
    (hHA : H ≤ normalizer (A : Set G)) (hHZ : H ≤ normalizer (Z : Set G))
    [(Z.subgroupOf A).Normal] : H →* MulAut (A ⧸ Z.subgroupOf A) :=
  Classical.choose (exists_quotient_conjugation_action H A Z hHA hHZ inferInstance)

/-- The action on every quotient representative is ambient conjugation. -/
theorem quotientAction_apply {G : Type*} [Group G] (H A Z : Subgroup G)
    (hHA : H ≤ normalizer (A : Set G)) (hHZ : H ≤ normalizer (Z : Set G))
    [(Z.subgroupOf A).Normal] (h : H) (a : A) :
    quotientAction H A Z hHA hHZ h (QuotientGroup.mk' (Z.subgroupOf A) a) =
      QuotientGroup.mk' (Z.subgroupOf A)
        ⟨(h : G) * a * (h : G)⁻¹, (hHA h.property a).mp a.property⟩ :=
  Classical.choose_spec (exists_quotient_conjugation_action H A Z hHA hHZ inferInstance) h a

/-- The action kernel is exactly the relative quotient centralizer. -/
theorem quotientAction_ker {G : Type*} [Group G] (H A Z : Subgroup G)
    (hHA : H ≤ normalizer (A : Set G)) (hHZ : H ≤ normalizer (Z : Set G))
    [(Z.subgroupOf A).Normal] [(Z.subgroupOf H).Normal] (hAH : A ≤ H) :
    (quotientAction H A Z hHA hHZ).ker = quotientCentralizer H A Z := by
  ext h
  rw [MonoidHom.mem_ker, mem_quotientCentralizer_iff H A Z hAH]
  constructor
  · intro he a ha
    have hfix := congrArg (fun e : MulAut (A ⧸ Z.subgroupOf A) =>
      e (QuotientGroup.mk' (Z.subgroupOf A) ⟨a, ha⟩)) he
    rw [quotientAction_apply] at hfix
    have hc := QuotientGroup.eq_iff_div_mem.mp hfix
    change (h : G) * a * (h : G)⁻¹ / a ∈ Z at hc
    have hi := Z.inv_mem hc
    simpa only [commutatorElement_def, div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc] using hi
  · intro hc
    apply MulEquiv.ext
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ x
    rw [quotientAction_apply]
    apply QuotientGroup.eq_iff_div_mem.mpr
    have hi := Z.inv_mem (hc a a.property)
    change (h : G) * (a : G) * (h : G)⁻¹ / (a : G) ∈ Z
    simpa only [commutatorElement_def, div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc] using hi

end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup

end
