module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour.MarkedAction.NaturalSection.Models
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.FlagTypes.ComponentAction.ProductRows.Groups
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.Recognition.ClassifiedComponent.Groups

/-!
# Excluding the product and outer alternatives for a symplectic component

A component lies in one of the two literal direct factors. A quasisimple
SL₂ or SL₃ factor must equal its contained component, contradicting the
actual symplectic marking. Small SL₂(2) and S₅ factors are too small.
In the corrected outer A₆–C₃ configuration, the existing perfectness
argument places the component in the literal A₆ factor.

Thus every nonquasisimple adequate B.5.6 alternative is excluded without
module splitting or assumptions on the order of the outer generator.
Source: Aschbacher–Smith B.5.6(3–5), printed p.105; application before
13.6.14 and in 13.6.19, printed pp.929–931.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.SourceInduction
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour.MarkedAction.NaturalSection
variable {D : Type*} [Group D] [Finite D] {C A B : Subgroup D}
variable {F : Type*} [Field F] [Finite F] {m : ℕ}

private theorem no_small_overgroup (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (mark : C ≃* Sp F) (hCA : C ≤ A) (hA : Nat.card A ≤ 20160) : False := by
  have h := card_gt_small hF hm
  rw [← Nat.card_congr mark.toEquiv] at h
  have hl := (Nat.card_le_card_of_injective (inclusion hCA) (inclusion_injective hCA)).trans hA
  omega

omit [Finite D] in
private theorem component_eq_of_quasisimple (hC : IsComponent D C) (hCA : C ≤ A)
    [IsQuasisimple A] : C = A := by
  have ht : IsComponent A ⊤ :=
    ⟨IsSubnormal.top, IsQuasisimple.of_mulEquiv (topEquiv).symm⟩
  exact le_antisymm hCA (subgroupOf_eq_top.mp ((hC.subgroupOf hCA).eq_of_le ht le_top))

private theorem slTwo_quasisimple (E : BinaryField) (hn : 2 ≤ E.degree) :
    IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) E.Carrier) := by
  have hcard : 4 ≤ Nat.card E.Carrier := by
    rw [E.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hn
  have hfield : ∃ a : E.Carrier, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
    obtain ⟨x, hx⟩ : IsCyclic E.Carrierˣ := inferInstance
    refine ⟨x, Units.ne_zero x, fun h ↦ ?_⟩
    grw [Nat.card_eq_card_units_add_one E.Carrier,
      ← orderOf_eq_card_of_forall_mem_zpowers hx,
      orderOf_le_of_pow_eq_one zero_lt_two (Units.ext <| by simpa using h)] at hcard
    omega
  exact { toIsPerfect := ⟨Matrix.SL2.commutator_eq_top hfield.choose_spec.1 hfield.choose_spec.2⟩
          simple := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hcard }

private theorem no_linearTwo_factor (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (mark : C ≃* Sp F) (hC : IsComponent D C) (hCA : C ≤ A)
    (E : BinaryField) (e : A ≃* Matrix.SpecialLinearGroup (Fin 2) E.Carrier) : False := by
  by_cases hn : E.degree = 1
  · apply no_small_overgroup hF hm mark hCA
    rw [Nat.card_congr e.toEquiv, Atlas.card_sl_two, E.card_eq, hn]
    norm_num
  · let := slTwo_quasisimple E (by have := E.degree_pos; omega)
    let : IsQuasisimple A := IsQuasisimple.of_mulEquiv e.symm
    exact not_linearTwo hF (by omega) E ⟨mark.symm.trans
      ((MulEquiv.subgroupCongr (component_eq_of_quasisimple hC hCA)).trans e)⟩

omit [Finite D] in
private theorem no_linearThree_factor (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (mark : C ≃* Sp F) (hC : IsComponent D C) (hCA : C ≤ A)
    (E : BinaryField) (e : A ≃* Matrix.SpecialLinearGroup (Fin 3) E.Carrier) : False := by
  let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 3) E.Carrier) :=
    { toIsPerfect := Atlas.sl_perfect 3 (by decide)
      simple := Atlas.psl_simple_high_rank 3 (by decide) }
  let : IsQuasisimple A := IsQuasisimple.of_mulEquiv e.symm
  exact not_linearThree hF (by omega) E ⟨mark.symm.trans
    ((MulEquiv.subgroupCongr (component_eq_of_quasisimple hC hCA)).trans e)⟩

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V}

private theorem no_source_factor (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (mark : C ≃* Sp F) (hC : IsComponent D C) (hCA : C ≤ A)
    {U : Subrepresentation ρ} (a : SourceFactorCase ρ A U) : False := by
  cases a with
  | natural _ h =>
    cases h with
    | linearTwo E hn =>
      obtain ⟨e⟩ := hn
      exact no_linearTwo_factor hF hm mark hC hCA E e.groupEquiv
    | symmetricFive hn =>
      obtain ⟨e⟩ := hn
      apply no_small_overgroup hF hm mark hCA
      rw [Nat.card_congr e.groupEquiv.toEquiv, Nat.card_perm, Nat.card_fin]
      norm_num [Nat.factorial]
    | linearThree E _ hn =>
      obtain ⟨e⟩ := hn
      exact no_linearThree_factor hF hm mark hC hCA E e.groupEquiv
  | doubleNatural E _ _ hn =>
    obtain ⟨e⟩ := hn
    exact no_linearThree_factor hF hm mark hC hCA E e.groupEquiv
  | exceptional _ e =>
    exact no_linearThree_factor hF hm mark hC hCA BinaryField.two e.natural.groupEquiv

theorem no_twoFactors (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (mark : C ≃* Sp F) (hC : IsComponent D C)
    (c : SourceTwoFactorCase ρ) : False := by
  rcases RankOneBorel.Replacement.NaturalRecognition.ClassifierCases.TwoFactor.component_le_factor hC c.product with h | h
  · exact no_source_factor hF hm mark hC h c.firstCase
  · exact no_source_factor hF hm mark hC h c.secondCase

theorem no_hyperplane (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (mark : C ≃* Sp F) (hC : IsComponent D C)
    (c : HyperplaneCase ρ) : False := by
  rcases RankOneBorel.Replacement.NaturalRecognition.ClassifierCases.TwoFactor.component_le_factor hC c.product with h | h
  · exact no_linearThree_factor hF hm mark hC h BinaryField.two c.firstEquiv
  · cases c.secondCase with
    | linearThree _ _ hn =>
      obtain ⟨e⟩ := hn
      exact no_linearThree_factor hF hm mark hC h BinaryField.two e.groupEquiv
    | linearTwo E hn =>
      obtain ⟨e⟩ := hn
      exact no_linearTwo_factor hF hm mark hC h E e.groupEquiv


/-- The corrected outer shape cannot contain the actual symplectic component. -/
theorem no_outerSixThree (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (mark : C ≃* Sp F) (hC : IsComponent D C)
    (c : OuterSixThreeShape D) : False := by
  apply no_small_overgroup hF hm mark
    (HigherFieldParabolics.G2.MarkedAction.Recognition.ClassifiedComponent.outer_component_le_first hC c)
  rw [Nat.card_congr c.firstEquiv.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  norm_num [Nat.factorial]

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour.MarkedAction.NaturalSection
