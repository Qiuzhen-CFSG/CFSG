module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.CenterFrattiniSource.IntrinsicStructure
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.CenterFrattiniSource.Representation
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.CenterFrattiniSource.SQTK

/-!
# A finite SQTK counterexample to the intrinsic center–Frattini implication

Let `X = (C₁₂₁ × C₁₂₁) ⋊ ⟨x,y⟩`, with the two prescribed matrices over
`ZMod 121`. The checked paired-generator graph identifies the actual
complement with `SL₂(5)` and proves its order is 120. We use these witnesses
to discharge every premise of the independent rank, K-group and intrinsic
structure certificates.

The resulting group has order 1,756,920, trivial two-core and trivial center.
Its generalized Fitting subgroup is the normal `C₁₂₁ × C₁₂₁`. The whole
group is a C-component, satisfies A.3.6(4) and every common A.3.6 assertion,
but fails `Z(X) = Φ(F*(X))` and every alternative of `Proposition121Four`.
In particular the radical index is two, its derived subgroup is the vector
kernel, and both required quotients are quasisimple. No structural clause is
dropped to obtain the counterexample.

The K-group certificate uses actual constructed carriers for all simple
sections. It transfers to any class containing those finite simple carriers;
it neither uses the universal class nor claims this partial catalogue is the
full source K. `intrinsic_counterexample` has no undischarged premise.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, Hypothesis A.3.4
and Proposition A.3.6, printed pp.43–45 (PDF pp.54–56), and Proposition
1.2.1(4), printed p.504 (PDF p.521). On p.45 the proof explicitly leaves
higher-exponent homocyclic groups possible when `p > 5`; p.504 adds the
center–Frattini equality while citing A.3.6.

This resolves the intrinsic implication only. The Chapter 1 setup also has
a QTKE ambient group `G`, a subgroup `H` with nontrivial two-core, and a
C-component `L` of `H`; its assertion concerns the image of `L` in
`H/O₂(H)`. We have not realized this candidate in that setup. To recover the
printed assertion, the Chapter 1 assembly must use additional ambient input
to rule out the residual A.3.6 nilpotent branch with noncentral Frattini
subgroup, including this inverted higher-exponent configuration. SQTK,
trivial two-core, C-component minimality and all common A.3.6 conclusions
alone cannot do so. No counterexample to the QTKE-local theorem is claimed.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02.CenterFrattiniSource

/-- The order of the actual semidirect product, using the checked matrix complement. -/
theorem candidate_order : Nat.card Candidate = 1756920 := by
  rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod, complement_card]
  change Nat.card (Fin 2 → ZMod 121) * 120 = _
  simp

/-- The checked complement order identifies the Fitting subgroup without a premise. -/
theorem candidate_fitting_eq_kernel : fittingSubgroup Candidate = kernel :=
  fitting_eq_kernel_of_coprime (by rw [complement_card]; decide)

/-- The generalized Fitting subgroup is exactly the concrete vector kernel. -/
theorem candidate_generalizedFitting_eq_kernel : generalizedFitting Candidate = kernel :=
  generalizedFitting_eq_kernel_of_coprime (by rw [complement_card]; decide)

/-- The concrete candidate is SQTK for the constructed known-simple carriers. -/
theorem candidate_isSQTK : IsSQTK CFSG.KnownSimple.IsConstructedCarrier Candidate :=
  candidate_isSQTK_constructed complementEquivSL5 complement_card

/-- The actual subgroup satisfies the complete A.3.6 conclusion, without
assuming a universal A.3.6 classification theorem. -/
theorem candidate_a36Conclusion : A36Conclusion (⊤ : Subgroup Candidate) :=
  ⟨.nilpotent (top_a36Nilpotent complementEquivSL5 complement_card),
    top_a36Common complementEquivSL5 complement_card⟩

/-- A fully instantiated finite counterexample. Both complement witnesses are
proved, and all intrinsic A.3.4 hypotheses and A.3.6 common clauses are retained. -/
theorem intrinsic_counterexample :
    Finite Candidate ∧
      IsSQTK CFSG.KnownSimple.IsConstructedCarrier Candidate ∧
      pCore 2 Candidate = ⊥ ∧
      (⊤ : Subgroup Candidate).IsCComponent ∧
      A36Nilpotent (⊤ : Subgroup Candidate) ∧
      A36Common (⊤ : Subgroup Candidate) ∧
      ¬ CenterFrattini (⊤ : Subgroup Candidate) ∧
      ¬ Proposition121Four (⊤ : Subgroup Candidate) :=
  ⟨inferInstance, candidate_isSQTK, twoCore_eq_bot,
    intrinsic_structure complementEquivSL5 complement_card⟩

/-- The same counterexample works for any class containing the constructed
finite simple carriers, in particular for an extension to the full source K. -/
theorem intrinsic_counterexample_of_catalogue {𝒦 : GroupClass}
    (h𝒦 : ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S],
      CFSG.KnownSimple.IsConstructedCarrier S → 𝒦 S) :
    Finite Candidate ∧ IsSQTK 𝒦 Candidate ∧ pCore 2 Candidate = ⊥ ∧
      (⊤ : Subgroup Candidate).IsCComponent ∧
      A36Nilpotent (⊤ : Subgroup Candidate) ∧
      A36Common (⊤ : Subgroup Candidate) ∧
      ¬ CenterFrattini (⊤ : Subgroup Candidate) ∧
      ¬ Proposition121Four (⊤ : Subgroup Candidate) :=
  ⟨inferInstance, candidate_isSQTK_of_catalogue h𝒦 complementEquivSL5 complement_card,
    twoCore_eq_bot, intrinsic_structure complementEquivSL5 complement_card⟩

/-- Even the full finite/SQTK/trivial-two-core/C-component hypotheses and the
complete A.3.6 conclusion do not force the additional equality in case (4). -/
theorem not_intrinsic_centerFrattini_implication :
    ¬ (∀ (X : Type) [Group X] [Finite X],
      IsSQTK CFSG.KnownSimple.IsConstructedCarrier X → pCore 2 X = ⊥ →
      ∀ K : Subgroup X, K.IsCComponent → A36Conclusion K → A36Nilpotent K →
        CenterFrattini K) := by
  intro h
  exact top_not_centerFrattini complement_card
    (h Candidate candidate_isSQTK twoCore_eq_bot ⊤
      (candidate_isCComponent complementEquivSL5) candidate_a36Conclusion
      (top_a36Nilpotent complementEquivSL5 complement_card))

/-- The intrinsic hypotheses do not imply the full four-case Chapter 1 list.
This is not a negation of the theorem in its QTKE ambient setup. -/
theorem not_intrinsic_proposition121Four_implication :
    ¬ (∀ (X : Type) [Group X] [Finite X],
      IsSQTK CFSG.KnownSimple.IsConstructedCarrier X → pCore 2 X = ⊥ →
      ∀ K : Subgroup X, K.IsCComponent → A36Conclusion K → Proposition121Four K) := by
  intro h
  exact top_not_proposition121Four complement_card
    (h Candidate candidate_isSQTK twoCore_eq_bot ⊤
      (candidate_isCComponent complementEquivSL5) candidate_a36Conclusion)

end CFSG.Quasithin.Chapter1.Section02.CenterFrattiniSource
