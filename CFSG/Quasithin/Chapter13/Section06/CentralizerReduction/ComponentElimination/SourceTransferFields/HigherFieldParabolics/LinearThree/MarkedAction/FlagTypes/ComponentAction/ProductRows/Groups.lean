module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.FlagTypes.ComponentAction.Restriction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.ClassifierCases.TwoFactor.Placement
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.Adequate

/-!
# Group comparisons for the nonquasisimple SL₃ component rows

An order-four unipotent element excludes an embedding of characteristic-two
SL₃ in characteristic-two SL₂. The actual SL₃ order formula gives order greater
than 1080 over fields larger than two, excluding the small factor actors.
The component calculus identifies a component contained in an SL₃ factor with
that factor itself. In the outer A₆–C₃ shape, perfectness places the component
inside the product of order 1080: the quotient is cyclic by generation, with
no assumption on the order of the outer generator or on a module splitting.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.6(3–5),
printed p.105; application before 13.6.14 and in 13.6.19, pp.929–931.
The matrix order and simplicity results retain the attribution in their imports.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Matrix
open scoped MatrixGroups CharTwo
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.ComponentAction.ProductRows
open ChapterB.QuasisimpleSource ChapterB.SourceInduction

private theorem sl_three_order_four (F : Type*) [Field F] [CharP F 2] :
    ∃ g : SL(3,F), orderOf g = 4 := by
  let g := SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : F) *
    SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) (1 : F)
  have hs : g ^ 2 = SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) (1 : F) := by
    apply Subtype.ext
    simp [g, pow_two, SpecialLinearGroup.transvection_coe, mul_add, add_mul]
    ext a b
    simp only [Matrix.add_apply]
    abel_nf
    simp
  have hn : g ^ 2 ≠ 1 := by
    rw [hs]
    intro h
    have hh := congrArg (fun x : SL(3,F) => x 0 2) h
    simp [SpecialLinearGroup.transvection_coe] at hh
  have hf : g ^ 4 = 1 := by
    rw [show 4 = 2 * 2 by decide, pow_mul, hs, pow_two,
      ← SpecialLinearGroup.transvection_add, CharTwo.add_self_eq_zero,
      SpecialLinearGroup.transvection_coeff_zero]
  exact ⟨g, @orderOf_eq_prime_pow _ _ g 1 2 ⟨Nat.prime_two⟩ hn hf⟩

/-- The order-four Jordan block rules out every even-field SL₂ target. -/
theorem not_injective_linearTwo {F E : Type*} [Field F] [CharP F 2]
    [Field E] [Finite E] [CharP E 2] (f : SL(3,F) →* SL(2,E))
    (hf : Function.Injective f) : False := by
  obtain ⟨g,hg⟩ := sl_three_order_four F
  exact CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.sl_order_ne_four
    (f g) ((orderOf_injective f hf g).trans hg)

/-- Count the actual cover, retaining its scalar kernel. -/
theorem card_sl_three (F : Type*) [Field F] [Finite F] :
    Nat.card SL(3,F) = Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center SL(3,F))
  rw [Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin] at h
  exact h.trans (Matrix.PSL3.LinearThree.card_projective_mul_scalar F)

/-- Even the smallest allowed field gives an order exceeding the outer product. -/
theorem large_card {F : Type*} [Field F] [Finite F] {m : ℕ}
    (hF : Nat.card F = 2 ^ m) (hm : 1 < m) : 1080 < Nat.card SL(3,F) := by
  rw [card_sl_three]
  have hq : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ m by omega)
  have hle := Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.pow_le_pow_left hq 3)
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 3) 1))
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
  exact lt_of_lt_of_le (by norm_num : 1080 < 4 ^ 3 * (4 ^ 3 - 1) * (4 ^ 2 - 1)) hle

/-- Exclude embeddings into the small actors used in these source rows. -/
theorem not_injective_small {F H : Type*} [Field F] [Finite F] [Finite H] {m : ℕ}
    (hF : Nat.card F = 2 ^ m) (hm : 1 < m) (hH : Nat.card H ≤ 1080)
    (f : SL(3,F) → H) (hf : Function.Injective f) : False :=
  (not_lt_of_ge ((Nat.card_le_card_of_injective f hf).trans hH)) (large_card hF hm)

/-- Containment in an actual quasisimple SL₃ factor forces equality. -/
theorem component_eq_linearThree {D : Type*} [Group D] {C A : Subgroup D}
    (hC : IsComponent D C) (hCA : C ≤ A) (E : BinaryField)
    (e : A ≃* SL(3,E.Carrier)) : C = A := by
  let : IsQuasisimple SL(3,E.Carrier) :=
    { toIsPerfect := Atlas.sl_perfect 3 (by decide)
      simple := Atlas.psl_simple_high_rank 3 (by decide) }
  let : IsQuasisimple A := IsQuasisimple.of_mulEquiv e.symm
  have ht : IsComponent A ⊤ :=
    ⟨IsSubnormal.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩
  exact le_antisymm hCA (subgroupOf_eq_top.mp ((hC.subgroupOf hCA).eq_of_le ht le_top))

/-- Perfectness and the cyclic quotient exclude the corrected outer shape. -/
theorem not_outerSixThree {D F : Type*} [Group D] [Finite D]
    [Field F] [Finite F] {C : Subgroup D} [IsQuasisimple C]
    {m : ℕ} (hF : Nat.card F = 2 ^ m) (hm : 1 < m) (e : C ≃* SL(3,F))
    (c : ChapterB.OuterSixThreeShape D) : False := by
  let := CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.outerSixThreeShape_product_normal c
  let := CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.outerSixThreeShape_quotient_isCyclic c
  let := IsCyclic.commGroup (α := D ⧸ (c.first ⊔ c.second))
  have hd : _root_.commutator D ≤ c.first ⊔ c.second :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  have hC : C ≤ c.first ⊔ c.second := by
    rw [← commutator_eq_self (H := C)]
    exact (commutator_mono le_top le_top).trans hd
  have hc : Nat.card (c.first ⊔ c.second : Subgroup D) = 1080 := by
    rw [← Nat.card_congr c.product.toEquiv, Nat.card_prod,
      Nat.card_congr c.firstEquiv.toEquiv, Nat.card_congr c.secondEquiv.toEquiv,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  exact not_injective_small hF hm hc.le
    (fun x => inclusion hC (e.symm x)) ((inclusion_injective hC).comp e.symm.injective)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.ComponentAction.ProductRows
