module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.SourceAlternatives
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelCases
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.CoverModels
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree


/-!
# Concrete carriers for the Borel component classification

The quasisimple models extracted from the complete FF action alternatives
are identified with the actual carriers in `BorelInner.ComponentModel`.
Perfectness excludes SL₂(2), identifies full perfect symplectic and G₂
models with their derived groups, and excludes symmetric direct factors.
The binary symplectic endpoint uses the proved derived-group isomorphism
with A₆. The triple-cover comparison reuses the proved cyclic-multiplier
uniqueness theorem and the actual even hexacode cover.

No field restriction from the later binary sieve is assumed. All field
exponents and genuine group equivalences are retained. The input here is
an output of the full action classification, not a universal classification
assumption consisting only of group labels.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.5(1)(iv)
and B.5.6, printed pp.104–105, with B.4.2, p.86, and B.5.1, p.99;
application in the proof of 15.3.49(k), p.1144. The A₆ cover comparison is
`Chapter13.Section08.Components.CoverModels.a6Triple_nonempty_mulEquiv`.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelSelection.Classification
universe u v
variable {D : Type u} [Group D] {E : Type v} [Group E]

/-- Output models are invariant under actual group isomorphisms. -/
theorem componentModel_of_equiv (e : D ≃* E) (h : ComponentModel E) : ComponentModel D := by
  cases h with
  | lie n h =>
    apply ComponentModel.lie n
    cases h with
    | linear_two hn F hc f => exact .linear_two hn F hc (f.map (e.trans ·))
    | linear_three hn F hc f => exact .linear_three hn F hc (f.map (e.trans ·))
    | symplectic hn F hc f => exact .symplectic hn F hc (f.map (e.trans ·))
    | g2 hn F hc f => exact .g2 hn F hc (f.map (e.trans ·))
    | binary_linear hn n hn' f => exact .binary_linear hn n hn' (f.map (e.trans ·))
  | alternating_seven f => exact .alternating_seven (f.map (e.trans ·))
  | triple_alternating_six f => exact .triple_alternating_six (f.map (e.trans ·))

private theorem not_perfect_perm (α : Type*) [Fintype α] [DecidableEq α] [Nontrivial α] :
    ¬ Group.IsPerfect (Equiv.Perm α) := by
  intro h
  let := h
  let : Group.IsPerfect ℤˣ := Group.IsPerfect.ofSurjective (Equiv.Perm.sign_surjective α)
  exact (by decide : (1 : ℤˣ) ≠ -1) (Subsingleton.elim _ _)

private noncomputable def perfectDerivedEquiv (E : Type*) [Group E] [Group.IsPerfect E] :
    E ≃* commutator E :=
  topEquiv.symm.trans (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top.symm)

/-- Perfectness excludes the binary SL₂ endpoint, which is the actual S₃. -/
theorem linearTwo_degree [Group.IsPerfect D] (F : BinaryField)
    (e : D ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier) : 2 ≤ F.degree := by
  by_contra hn
  have he : F.degree = 1 := by have := F.degree_pos; omega
  have hc : Nat.card F.Carrier = 2 := by rw [F.card_eq, he]; rfl
  let := Fintype.ofFinite F.Carrier
  let f : F.Carrier ≃+* ZMod 2 :=
    (ZMod.ringEquivOfPrime F.Carrier (by decide)
      (by simpa only [← Nat.card_eq_fintype_card] using hc)).symm
  obtain ⟨g⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  let a := e.trans ((Atlas.fieldEquivSL 2 f).trans g)
  exact not_perfect_perm (Fin 3) (Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective)

/-- Convert every quasisimple FF carrier to the literal Borel catalogue.
Perfectness supplies the derived-carrier comparison; no binary restriction is imposed. -/
theorem componentModel_of_quasisimpleModel [Finite D] [IsQuasisimple D]
    (h : QuasisimpleModel D) : ComponentModel D := by
  cases h with
  | linearTwo F e =>
    exact .lie F.degree (.linear_two (linearTwo_degree F e) F.Carrier F.card_eq
      ⟨e.trans (linearTwoProjectiveEquiv F)⟩)
  | linearThree F e =>
    exact .lie F.degree (.linear_three F.degree_pos F.Carrier F.card_eq ⟨e⟩)
  | symplecticFour F e =>
    let : Group.IsPerfect (Matrix.symplecticGroup (Fin 2) F.Carrier) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    exact .lie F.degree (.symplectic F.degree_pos F.Carrier F.card_eq
      ⟨e.trans (perfectDerivedEquiv _)⟩)
  | g2 F e =>
    let : Group.IsPerfect (Atlas.G2.Model F.Carrier) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    exact .lie F.degree (.g2 F.degree_pos F.Carrier F.card_eq
      ⟨e.trans (perfectDerivedEquiv _)⟩)
  | alternatingSix e =>
    exact .lie 1 (.symplectic (by decide) (ZMod 2) (by simp)
      ⟨e.trans binarySymplecticDerivedEquiv.symm⟩)
  | alternatingSeven e => exact .alternating_seven ⟨e⟩
  | tripleSix ec eq =>
    exact .triple_alternating_six
      (CFSG.Quasithin.Chapter13.Section08.Components.CoverModels.a6Triple_nonempty_mulEquiv
        ⟨inferInstance, ⟨ec⟩, ⟨eq⟩⟩)
  | g2DerivedTwo e => exact .lie 1 (.g2 (by decide) (ZMod 2) (by simp) ⟨e⟩)
  | linearFourTwo e =>
    exact .lie 1 (.binary_linear rfl 4 (Or.inl rfl)
      ⟨e.trans (binaryProjectiveEquiv 4 (by decide))⟩)
  | linearFiveTwo e =>
    exact .lie 1 (.binary_linear rfl 5 (Or.inr rfl)
      ⟨e.trans (binaryProjectiveEquiv 5 (by decide))⟩)

/-- In a perfect actor each B.5.6 direct factor is a quasisimple linear group.
The symmetric and degree-one cases are excluded using their abelian quotients. -/
theorem factor_classification [Finite D] [Group.IsPerfect D]
    (h : FactorModel D) : IsQuasisimple D ∧ ComponentModel D := by
  cases h with
  | linearTwo F e =>
    have hn := linearTwo_degree F e
    let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) F.Carrier) :=
      { toIsPerfect := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
        simple := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
          rw [F.card_eq]
          exact Nat.pow_le_pow_right (by decide : 0 < 2) hn) }
    let : IsQuasisimple D := IsQuasisimple.of_mulEquiv e.symm
    exact ⟨inferInstance, componentModel_of_quasisimpleModel (.linearTwo F e)⟩
  | symmetricFive e =>
    exact (not_perfect_perm (Fin 5)
      (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)).elim
  | linearThree F _ e =>
    let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) :=
      { toIsPerfect := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
        simple := Atlas.psl_simple_high_rank 3 (by decide) }
    let : IsQuasisimple D := IsQuasisimple.of_mulEquiv e.symm
    exact ⟨inferInstance, componentModel_of_quasisimpleModel (.linearThree F e)⟩

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelSelection.Classification
