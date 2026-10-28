module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.FlagTypes.ComponentAction.Restriction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.FlagTypes.ComponentAction.Quasisimple.ModelComparison
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.Homogeneity

/-!
# The higher-field SL₃ component in the quasisimple classifier branch

We exhaust the corrected B.4.2 irreducible list and all four B.5.1 action
alternatives using the actual group comparisons. The surviving quotient is a
natural SL₃ module or two identically marked copies. In the doubled case,
transvections give zero invariants on the model, and the literal central
quotient therefore retains the same repeated coordinates. Central extensions
of the original module and the component's possible nontrivial center remain
allowed. The marking is existential, so it also permits the dual coordinate
choice.

The source application uses the actual offender subgroup of the plus action,
with W_K elementary by containment in Uᵥ. It transports the component through
its genuine subgroup equivalence and returns the canonical plus moved quotient.
The parent assembly selects this branch and supplies its full corrected source
conclusion; no further model comparison or module hypothesis remains here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.1 and
B.5.6, printed pp.99–105, applied before 13.6.14 and in 13.6.19, pp.929–931.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.SourceInduction
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.ComponentAction.Quasisimple

private theorem no_small_equiv {C X : Type*} [Group C] [Group X]
    {F : Type*} [Field F] [Finite F] {m : ℕ}
    (hF : Nat.card F = 2 ^ m) (hm : 1 < m) (mark : C ≃* SL(3, F))
    (e : C ≃* X) (hx : Nat.card X ≤ 20160) : False := by
  have h := card_gt_small hF hm
  rw [← Nat.card_congr mark.toEquiv, Nat.card_congr e.toEquiv] at h
  omega

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {C H : Subgroup D}
    {F : Type*} [Field F] [Finite F] {m : ℕ}

/-- Every corrected irreducible source row except the natural SL₃ row is
excluded by the actual component isomorphism. -/
theorem irreducible_row (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (mark : C ≃* SL(3, F))
    (h : ProjectiveLine.IrreducibleActionCase ρ C H) :
    ∃ E : BinaryField, Nonempty (ActionEquiv (ρ.comp C.subtype) (linearNatural E 3)) := by
  cases h with
  | linearTwo E _ e _ _ =>
    exact (not_linearTwo hF (by omega) E ⟨mark.symm.trans e.groupEquiv⟩).elim
  | linearThree E _ e _ =>
    exact ⟨E, ⟨e⟩⟩
  | symplectic E _ _ e _ =>
    exact (not_symplecticFour hF (by omega) E ⟨mark.symm.trans e.groupEquiv⟩).elim
  | symplecticTwo e _ =>
    apply (no_small_equiv hF hm mark e.subgroupEquiv ?_).elim
    apply (Nat.card_le_card_of_injective _ (commutator
      (Matrix.symplecticGroup (Fin 2) (ZMod 2))).subtype_injective).trans
    rw [Theory.SpecificGroups.SymplecticFour.card_sp, Nat.card_zmod]
    norm_num
  | g2 E _ _ e _ _ =>
    exact (not_g2 hF (by omega) E ⟨mark.symm.trans e.groupEquiv⟩).elim
  | g2Two e _ _ =>
    apply (no_small_equiv hF hm mark e.subgroupEquiv ?_).elim
    apply (Nat.card_le_card_of_injective _ (commutator
      (Atlas.G2.Model (ZMod 2))).subtype_injective).trans
    rw [Atlas.G2.card_Model, Nat.card_zmod]
    norm_num
  | symmetric n hn e _ _ =>
    apply (no_small_equiv hF hm mark e.subgroupEquiv ?_).elim
    rcases hn with rfl | rfl <;>
      rw [nat_card_alternatingGroup, Nat.card_fin] <;> norm_num [Nat.factorial]
  | alternatingSix _ e _ _ =>
    apply (no_small_equiv hF hm mark e.groupEquiv ?_).elim
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  | alternatingSeven _ _ e _ _ _ =>
    apply (no_small_equiv hF hm mark e ?_).elim
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  | tripleSix _ a _ =>
    have hc : Nat.card C ≤ 20160 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center C),
        Nat.card_congr a.quotientEquiv.toEquiv, Nat.card_congr a.centerEquiv.toEquiv,
        nat_card_alternatingGroup]
      norm_num [Nat.factorial, Nat.card_congr
        (Multiplicative.toAdd : Multiplicative (ZMod 3) ≃ ZMod 3)]
    exact (no_small_equiv hF hm mark (MulEquiv.refl C) hc).elim
  | binaryLinear d hd _ e _ =>
    exact (not_binary_linear hF hm hd ⟨mark.symm.trans e.groupEquiv⟩).elim
  | orthogonalSix _ _ e _ _ =>
    apply (no_small_equiv hF hm mark e.groupEquiv ?_).elim
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  | symmetricEight _ e _ =>
    apply (no_small_equiv hF hm mark e.subgroupEquiv ?_).elim
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  | exteriorFive _ _ e _ _ _ =>
    exact (not_binary_linear hF hm (Or.inr rfl) ⟨mark.symm.trans e⟩).elim


private def compose {A B H U W X : Type*} [Group A] [Group B] [Group H]
    [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup X] [Module (ZMod 2) X]
    {α : Representation (ZMod 2) A U} {β : Representation (ZMod 2) B W}
    {γ : Representation (ZMod 2) H X}
    (e : ActionEquiv α β) (f : ActionEquiv β γ) : ActionEquiv α γ :=
  ⟨e.groupEquiv.trans f.groupEquiv, e.linearEquiv.trans f.linearEquiv,
    fun g v => (congrArg f.linearEquiv (e.intertwines g v)).trans
      (f.intertwines (e.groupEquiv g) (e.linearEquiv v))⟩

private def oneCopy {A U : Type*} [Group A] [AddCommGroup U] [Module (ZMod 2) U]
    (α : Representation (ZMod 2) A U) : ActionEquiv α (repeated α 1) where
  groupEquiv := MulEquiv.refl A
  linearEquiv := (LinearEquiv.piUnique (ZMod 2) (fun _ : Fin 1 => U)).symm
  intertwines _ _ := rfl

/-- Repeated natural coordinates descend to the literal central quotient.
The vanishing fixed space is proved in the model and transported along the
same marking on every copy; no complement in the original module is assumed. -/
theorem repeated_on_quotient (s : MovedSection ρ C) (E : BinaryField) {d r : ℕ}
    (hd : 2 ≤ d)
    (h : IsRepeatedLinearNatural (s.space.toRepresentation.comp C.subtype) E d r) :
    IsRepeatedLinearNatural (s.action.comp C.subtype) E d r := by
  obtain ⟨e⟩ := h
  have hz := ExtensionConsequences.invariants_of_equiv e
    (ExtensionConsequences.repeated_invariants r (ExtensionConsequences.linearNatural_invariants E hd))
  exact ⟨compose (ExtensionConsequences.movedQuotientEquiv s hz) e⟩

/-- Exhaust the four B.5.1 action alternatives and all corrected B.4.2 rows.
Only a natural quotient or the quotient of two identically marked natural
copies survives for a higher-field SL₃ component. -/
theorem action_case (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (mark : C ≃* SL(3, F)) (s : MovedSection ρ C)
    (h : ProjectiveLine.QuasisimpleActionCase ρ C s) :
    ∃ (E : BinaryField) (r : ℕ), (r = 1 ∨ r = 2) ∧
      IsRepeatedLinearNatural (s.action.comp C.subtype) E 3 r := by
  cases h with
  | irreducible _ _ _ h _ =>
    obtain ⟨E, ⟨e⟩⟩ := irreducible_row hF hm mark h
    exact ⟨E, 1, Or.inl rfl, ⟨compose e (oneCopy (linearNatural E 3))⟩⟩
  | doubleThree E _ e _ _ =>
    exact ⟨E, 2, Or.inr rfl, repeated_on_quotient s E (by decide) ⟨e⟩⟩
  | naturalDual d hd _ hn =>
    obtain ⟨e⟩ := hn
    exact (not_binary_linear hF hm hd ⟨mark.symm.trans e.groupEquiv⟩).elim
  | repeatedNatural d r hd _ _ _ hn =>
    obtain ⟨e⟩ := hn
    exact (not_binary_linear hF hm hd ⟨mark.symm.trans e.groupEquiv⟩).elim

/-- Extraction from the full corrected source conclusion on any construction
of the canonical moved section. Once that conclusion is supplied, the FF,
normality and quasisimplicity hypotheses require no further use here. -/
theorem repeated_natural (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (mark : C ≃* SL(3, F)) (s : MovedSection ρ C)
    (c : ProjectiveLine.QuasisimpleSourceConclusion ρ C) :
    ∃ (E : BinaryField) (r : ℕ), 0 < r ∧
      IsRepeatedLinearNatural (s.action.comp C.subtype) E 3 r := by
  obtain ⟨E, r, hr, he⟩ := action_case hF hm mark c.sectionData c.clause_one
  rw [movedSection_unique c.sectionData s] at he
  exact ⟨E, r, by omega, he⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.ComponentAction.Quasisimple

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction
open ComponentSelection
universe u
variable {G : Type u} [Group G] [Finite G]
variable (K L T : Subgroup G) (z v : G)
variable (hL : Tv T v ≤ normalizer (Lv L v : Set G))
variable (hz : Tv T v ≤ centralizer ({z} : Set G))
variable [IsElementaryAbelian 2 (Uv z v)]

/-- The quasisimple branch of the actual plus offender classifier supplies the
repeated natural quotient used in 13.6.19. W_K inherits its elementary structure
from Uᵥ; the component marking passes through the literal subgroup equivalence.
The full corrected classifier conclusion is the earlier-source input selected
by the parent component-action assembly. -/
theorem plus_component_repeated_of_quasisimple (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hU : Uv z v ≤ (Gv v).pCoreIn 2)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    {F : Type*} [Field F] [Finite F] {m : ℕ}
    (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (e : plusImage K L T z v hL hz K ≃* SL(3, F)) :
    letI : IsElementaryAbelian 2 (WK K L T z v) :=
      IsElementaryAbelian.of_le (WK_le_Uv K L T z v hK.1.1)
    let ρ := plusRepresentation K L T z v hL hz
    let I := offenderSubgroup ρ
    let C := plusImage K L T z v hL hz K
    ProjectiveLine.QuasisimpleSourceConclusion (ρ.comp I.subtype) (C.subgroupOf I) →
      ∃ (E : BinaryField) (r : ℕ), 0 < r ∧
        IsRepeatedLinearNatural
          ((plusComponentSection K L T z v hL hz hK hn).action.comp C.subtype) E 3 r := by
  let : IsElementaryAbelian 2 (WK K L T z v) :=
    IsElementaryAbelian.of_le (WK_le_Uv K L T z v hK.1.1)
  intro ρ I C c
  have hCI : C ≤ I := plus_component_le_offender K L T z v hL hz hK hn hU hSyl
  let s := plusComponentSection K L T z v hL hz hK hn
  let t := ComponentAction.restrictSection s I hCI
  obtain ⟨E, r, hr, he⟩ := ComponentAction.Quasisimple.repeated_natural hF hm
    ((subgroupOfEquivOfLe hCI).trans e) t c
  exact ⟨E, r, hr, (ComponentAction.repeated_restrict_iff s I hCI E 3 r).mp he⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction
