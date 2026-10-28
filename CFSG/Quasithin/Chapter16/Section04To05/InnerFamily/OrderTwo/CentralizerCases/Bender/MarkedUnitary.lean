module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.CentralizerCases.Bender.MarkedActions
public import Theory.SpecificGroups.SU3.GraphFixedResidual
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport

/-!
# Marked projective unitary graph residuals

An actual Hermitian basis change gives a standard projective unitary model
of the central quotient, with both source field cardinalities preserved.
Once the earlier outer-involution classification conjugates the induced
action to the graph action, its embedded residual and full pointwise fixer
transport to the actual graph-fixed subgroup. The conjugacy is explicit;
it is not asserted here or inferred from an abstract fixed-group type.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.4(6) and 16.4.9(1), printed pp.1171 and 1189.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.HermitianForm
open BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter
namespace CFSG.Quasithin.Chapter16.Intersections.OrderTwo.CentralizerCases.Bender
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- A genuine basis change standardizes the model while retaining the quotient map. -/
theorem unitary_standard_marking (hG : HasEvenTypeCentralizers G)
    (h : IntersectionSetup T z L g R) {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSU (L ⧸ pCore 2 L) 3 (2 ^ n)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (J : HermitianForm 3 F)
      (_ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
      (_ : (L ⧸ center L) ≃* ProjectiveSpecialUnitaryMatrixGroup J),
      Nat.card F = (2 ^ n) ^ 2 ∧ Nat.card {x : F // J.conj x = x} = 2 ^ n := by
  let := h.component.quasisimple
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := hmodel
  have hfixed : Nat.card {x : F // J.conj x = x} = 2 ^ n :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  obtain ⟨f⟩ := FormTransport.exists_projectiveEquiv J (2 ^ n) hcard hfixed
  let e' := ((LiePreliminaries.centerQuotientEquivTwoCore
    (component_oddCore hG h.toCentralComponentSetup)).trans e).trans f
  exact ⟨F, hF, hfin, FormTransport.standardForm J, rfl, e', hcard, hfixed⟩

/-- A supplied graph conjugacy identifies the actual residual and transports its full fixer. -/
theorem unitary_marked_graph_residual {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hG : HasEvenTypeCentralizers G) (h : IntersectionSetup T z L g R)
    (J : HermitianForm 3 F) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (e : (L ⧸ center L) ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    {n : ℕ} (hn : 2 ≤ n)
    (hfixed : Nat.card {x : F // J.conj x = x} = 2 ^ n)
    (hrn : r ∈ normalizer (L : Set G))
    (c : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hc : modelAction L e (actionElement L r hrn) =
      MulAut.congr c (projectiveGraphAut J hJ)) :
    modelResidual L e r = (projectiveGraphAut J hJ).fixedSubgroup.map c.toMonoidHom ∧
      Nat.card (fixingSubgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
        (modelResidual L e r : Set (ProjectiveSpecialUnitaryMatrixGroup J))) =
      Nat.card (fixingSubgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
        ((projectiveGraphAut J hJ).fixedSubgroup : Set (ProjectiveSpecialUnitaryMatrixGroup J))) := by
  let := h.component.quasisimple
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_equiv (L ⧸ center L) e.toEquiv
  have he : LiePreliminaries.fixedTwoResidual
      (ProjectiveSpecialUnitaryMatrixGroup J) (projectiveGraphAut J hJ) =
      (projectiveGraphAut J hJ).fixedSubgroup :=
    graph_embeddedFixedResidual_eq_fixed J hJ hn hfixed
  have hodd := component_oddCore hG h.toCentralComponentSetup
  constructor
  · rw [modelResidual_eq_map_of_congr hodd e hrn _ c hc, he]
  · rw [modelResidual_fixer_card_of_congr hodd e hrn _ c hc, he]
end CFSG.Quasithin.Chapter16.Intersections.OrderTwo.CentralizerCases.Bender
