module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.Recognition.ClassifiedComponent.Transport
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Theory.AtlasPort.LinearGroups.G2.Order

/-!
# Exhausting the quasisimple B.5.1 action alternatives

The actual marked component is F*(D) when that subgroup is quasisimple.
The full projective-line B.4.2 list then has a unique surviving group family:
variable-field alternatives are excluded by ModelSeparation and the remaining
actors have order at most |SL₅(2)|. The same comparisons exclude the three
reducible B.5.1 alternatives. In the G₂ row, equality of field cardinalities
constructs the field isomorphism and transports the natural quotient action.

The result concerns every literal moved/fixed section of the component action;
it assumes neither irreducibility nor a previously selected G₂ row.
Source: Aschbacher–Smith B.4.2 and B.5.1, printed pp.86 and 99, as used before
13.6.14 and in 13.6.19, pp.929–931. The order formulas reuse the attributed
ATLAS ports imported above.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.SourceInduction
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.Recognition.ClassifiedComponent
private theorem sl_card_mul (F : Type*) [Field F] [Finite F]
    (d : ℕ) [NeZero d] :
    Nat.card (Matrix.SpecialLinearGroup (Fin d) F) * (Nat.card F - 1) =
      ∏ i : Fin d, (Nat.card F ^ d - Nat.card F ^ (i : ℕ)) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    (center (Matrix.SpecialLinearGroup (Fin d) F)),
    Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin]
  exact Atlas.ExceptionalSupport.card_psl_mul d

private theorem small_binary_linear {d : ℕ} (hd : d = 4 ∨ d = 5) :
    Nat.card (Matrix.SpecialLinearGroup (Fin d) (ZMod 2)) ≤ 9999360 := by
  rcases hd with rfl | rfl
  · have h := sl_card_mul (ZMod 2) 4
    norm_num only [Nat.card_zmod, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ,
      Finset.prod_empty, mul_one] at h
    omega
  · have h := sl_card_mul (ZMod 2) 5
    norm_num only [Nat.card_zmod, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ,
      Finset.prod_empty, mul_one] at h
    omega

private theorem small_alternating {n : ℕ} (hn : n ≤ 8) :
    Nat.card (alternatingGroup (Fin n)) ≤ 9999360 := by
  apply (Nat.card_le_card_of_injective _ (alternatingGroup (Fin n)).subtype_injective).trans
  rw [Nat.card_perm, Nat.card_fin]
  exact (Nat.factorial_le hn).trans (by norm_num [Nat.factorial])

theorem no_small_equiv {C X : Type*} [Group C] [Group X]
    {F : BinaryField} (sep : ModelSeparation F) (mark : C ≃* Atlas.G2.Model F.Carrier)
    (e : C ≃* X) (hx : Nat.card X ≤ 9999360) : False := by
  have h := sep.large_order
  rw [← Nat.card_congr mark.toEquiv, Nat.card_congr e.toEquiv] at h
  omega

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {C H : Subgroup D}
    {F : BinaryField}

theorem irreducible_row (sep : ModelSeparation F)
    (mark : C ≃* Atlas.G2.Model F.Carrier)
    (h : ProjectiveLine.IrreducibleActionCase ρ C H) :
    Nonempty (ActionEquiv (ρ.comp C.subtype) (binaryG2 F)) := by
  cases h with
  | linearTwo E _ e _ _ =>
    exact (sep.not_linearTwo E ⟨mark.symm.trans e.groupEquiv⟩).elim
  | linearThree E _ e _ =>
    exact (sep.not_linearThree E ⟨mark.symm.trans e.groupEquiv⟩).elim
  | symplectic E _ _ e _ =>
    exact (sep.not_symplecticFour E ⟨mark.symm.trans e.groupEquiv⟩).elim
  | symplecticTwo e _ =>
    apply (no_small_equiv sep mark e.subgroupEquiv ?_).elim
    apply (Nat.card_le_card_of_injective _ (commutator
      (Matrix.symplecticGroup (Fin 2) (ZMod 2))).subtype_injective).trans
    rw [Theory.SpecificGroups.SymplecticFour.card_sp, Nat.card_zmod]
    norm_num
  | g2 E _ _ e _ _ =>
    have he := sep.field_order E ⟨e.groupEquiv.symm.trans mark⟩
    exact ⟨compose e (sameFieldActionEquiv he)⟩
  | g2Two e _ _ =>
    apply (no_small_equiv sep mark e.subgroupEquiv ?_).elim
    apply (Nat.card_le_card_of_injective _ (commutator
      (Atlas.G2.Model (ZMod 2))).subtype_injective).trans
    rw [Atlas.G2.card_Model, Nat.card_zmod]
    norm_num
  | symmetric n hn e _ _ =>
    exact (no_small_equiv sep mark e.subgroupEquiv (small_alternating (by omega))).elim
  | alternatingSix _ e _ _ =>
    exact (no_small_equiv sep mark e.groupEquiv (small_alternating (by decide))).elim
  | alternatingSeven _ _ e _ _ _ =>
    exact (no_small_equiv sep mark e (small_alternating (by decide))).elim
  | tripleSix _ a _ =>
    have hc : Nat.card C ≤ 9999360 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center C),
        Nat.card_congr a.quotientEquiv.toEquiv, Nat.card_congr a.centerEquiv.toEquiv,
        nat_card_alternatingGroup]
      norm_num [Nat.factorial, Nat.card_congr
        (Multiplicative.toAdd : Multiplicative (ZMod 3) ≃ ZMod 3)]
    exact (no_small_equiv sep mark (MulEquiv.refl C) hc).elim
  | binaryLinear d hd _ e _ =>
    exact (no_small_equiv sep mark e.groupEquiv (small_binary_linear hd)).elim
  | orthogonalSix _ _ e _ _ =>
    exact (no_small_equiv sep mark e.groupEquiv (small_alternating (by decide))).elim
  | symmetricEight _ e _ =>
    exact (no_small_equiv sep mark e.subgroupEquiv (small_alternating (by decide))).elim
  | exteriorFive _ _ e _ _ _ =>
    exact (no_small_equiv sep mark e (small_binary_linear (Or.inr rfl))).elim

theorem quasisimple_action (sep : ModelSeparation F)
    (mark : C ≃* Atlas.G2.Model F.Carrier) (s : MovedSection ρ C)
    (h : ProjectiveLine.QuasisimpleActionCase ρ C s)
    (t : MovedSection (ρ.comp C.subtype) ⊤) :
    Nonempty (ActionEquiv t.action (binaryG2 F)) := by
  cases h with
  | irreducible _ _ _ h _ =>
    obtain ⟨e⟩ := irreducible_row sep mark h
    exact ⟨compose (restrictSectionEquiv s t) e⟩
  | doubleThree E _ e _ _ =>
    exact (sep.not_linearThree E ⟨mark.symm.trans e.groupEquiv⟩).elim
  | naturalDual d hd _ hn =>
    obtain ⟨e⟩ := hn
    exact (no_small_equiv sep mark e.groupEquiv (small_binary_linear hd)).elim
  | repeatedNatural d r hd _ _ _ hn =>
    obtain ⟨e⟩ := hn
    exact (no_small_equiv sep mark e.groupEquiv (small_binary_linear hd)).elim

variable [Finite D]

theorem component_eq_fitting (hC : IsComponent D C)
    (hq : IsQuasisimple (generalizedFitting D)) : C = generalizedFitting D :=
  hC.eq_of_le ⟨(inferInstance : (generalizedFitting D).Normal).isSubnormal, hq⟩
    (component_le_generalizedFitting D C hC)

theorem quasisimple_branch (sep : ModelSeparation F)
    (hC : IsComponent D C) (mark : C ≃* Atlas.G2.Model F.Carrier)
    (hq : IsQuasisimple (generalizedFitting D))
    (q : ProjectiveLine.QuasisimpleSourceConclusion ρ (generalizedFitting D))
    (t : MovedSection (ρ.comp C.subtype) ⊤) :
    Nonempty (ActionEquiv t.action (binaryG2 F)) := by
  have he := component_eq_fitting hC hq
  subst C
  exact quasisimple_action sep mark q.sectionData q.clause_one t

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.Recognition.ClassifiedComponent
