module

public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five.MaximalExtension
public import Theory.SpecificGroups.SU3.ProjectiveEntrywiseAction
public import ABG.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The two concrete maximal-subgroup calculations for PSU₃(5)

The inner calculation asks for an actual embedding of A₇ in the standard
projective matrix group, a proof that its image is maximal, and three
involutory generators of A₇. The outer calculation asks for an actual S₇
embedding in the automorphism group, maximal inside the extension generated
by the inner automorphisms and the specified entrywise involution. Its
three generators must be literal inner conjugates of that involution.

These are unproved input predicates, not assertions of existence. The
consumer `Five` supplies arbitrary-form transport, inner involution fusion,
outer normalization, and the fourth conjugate. Thus neither calculation
requires independent simplicity certification or representation theory.

Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
manuscript pp.10–11, used in Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public noncomputable section
open Subgroup
namespace BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The identity-Gram form over the actual quadratic field GF(25). -/
abbrev standardForm := ABG.unitaryForm 3 5 1 (by decide)

/-- The concrete projective special unitary matrix image. -/
abbrev StandardGroup := ProjectiveSpecialUnitaryMatrixGroup standardForm

/-- The source A₇ calculation, including its genuine embedding and generators. -/
def InnerModel : Prop :=
  ∀ [IsSimpleGroup StandardGroup],
    ∃ f : alternatingGroup (Fin 7) →* StandardGroup,
      Function.Injective f ∧ IsCoatom f.range ∧
      ∃ t : Fin 3 → alternatingGroup (Fin 7),
        (∀ i, orderOf (t i) = 2) ∧ closure (Set.range t) = ⊤

/-- The source S₇ calculation on the normalized antidiagonal model.
The conjugators are in PSU₃, and maximality is relative to the involution's
own extension, not the full automorphism group. -/
def OuterModel : Prop :=
  ∀ {E : Type} [Field E] [Finite E] (J : HermitianForm 3 E)
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)],
    Nat.card E = 5 ^ 2 → (∀ x, J.conj x = x ^ 5) →
    J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] →
    ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
      a ≠ 1 → a ^ 2 = 1 → J.IsEntrywiseConjugation a →
      ∃ f : Equiv.Perm (Fin 7) →* MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
        Function.Injective f ∧ f.range ⋖ MulAut.singleInnerExtension a ∧
        ∃ t : Fin 3 → Equiv.Perm (Fin 7), closure (Set.range t) = ⊤ ∧
          ∀ i, ∃ s : ProjectiveSpecialUnitaryMatrixGroup J,
            MulAut.conj s * a * (MulAut.conj s)⁻¹ = f (t i)

end BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five
