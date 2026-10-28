module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract
public import CFSG.Quasithin.ChapterB.Section05.OuterSixThreeShape

/-!+# The separate consumer-adequate classification target

The input is exactly B.5.3, including a genuine finite SQTK cover. The output
retains the trivial actor and all module clauses of B.5.6(1), (2), (3), (5).
Only the disputed whole-space splitting in (4) is replaced by the literal
`OuterSixThreeShape`. No implication to the old full classification is asserted.

In (3), the summands live in the quotient by the global fixed space. In (5),
the sum is inside the moved space and the remaining quotient has dimension one.
Every natural-module claim includes an actor isomorphism and an intertwiner.
These definitions publish a target, not a proof of classification.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.3–B.5.12, printed pp.104–110; B.4.8(3), p.91.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction
open QuasisimpleSource
universe u v

/-- The cover and quotient map are actual groups and maps. -/
structure SQTKQuotient (K : GroupClass.{u}) (D : Type u) [Group D] where
  Cover : Type u
  [coverGroup : Group Cover]
  [coverFinite : Finite Cover]
  kernel : Subgroup Cover
  [kernelNormal : kernel.Normal]
  sqtk : IsSQTK K Cover
  equiv : (Cover ⧸ kernel) ≃* D

attribute [instance] SQTKQuotient.coverGroup SQTKQuotient.coverFinite
  SQTKQuotient.kernelNormal

/-- The literal finite, faithful, offender-generated action of B.5.3. -/
structure FFHypothesis (K : GroupClass.{u}) {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) : Prop where
  finite_module : Module.Finite (ZMod 2) V
  faithful : Function.Injective ρ
  twoCore : pCore 2 D = ⊥
  generated : offenderSubgroup ρ = ⊤
  quotient : Nonempty (SQTKQuotient K D)

variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

/-- Multiplication of the two original inclusions is the product isomorphism. -/
structure InternalProduct (A B : Subgroup D) where
  equiv : (A × B) ≃* D
  apply_eq : ∀ a b, equiv (a, b) = (a : D) * (b : D)

/-- B.5.6(2), with the splitting in the original module. -/
structure SymmetricThreeCase where
  equiv : D ≃* Equiv.Perm (Fin 3)
  decomposition : IsCompl (moved ρ ⊤) ρ.invariants
  dimension : Module.finrank (ZMod 2) (moved ρ ⊤) = 2

/-- The natural actions allowed on an individual quotient summand. -/
inductive FactorNatural : Prop
  | linearTwo (F : BinaryField) (natural : IsLinearNatural ρ F 2)
  | symmetricFive (natural : IsSymmetricNatural ρ 5)
  | linearThree (F : BinaryField) (odd_degree : Odd F.degree)
      (natural : IsLinearNatural ρ F 3)

/-- B.5.6(3a–c) on the image of the specified ambient submodule.
The exceptional action retains every referenced B.4.8(3) clause. -/
inductive SourceFactorCase (A : Subgroup D) (U : Subrepresentation ρ) : Prop
  | natural (moved_eq : U.toSubmodule = moved ρ A)
      (natural : FactorNatural (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype))
  | doubleNatural (F : BinaryField) (odd_degree : Odd F.degree)
      (moved_eq : U.toSubmodule = moved ρ A)
      (natural : IsRepeatedLinearNatural
        (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype) F 3 2)
  | exceptional (moved_le : moved ρ A ≤ U.toSubmodule)
      (extension : FourDimensionalSource
        (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype))

/-- B.5.6(3) splits precisely `V / C_V(D)`. -/
structure SourceTwoFactorCase where
  first : Subgroup D
  second : Subgroup D
  product : InternalProduct first second
  firstSpace : Subrepresentation ρ
  secondSpace : Subrepresentation ρ
  decomposition : IsCompl ((fixed ρ).quotientImage firstSpace).toSubmodule
    ((fixed ρ).quotientImage secondSpace).toSubmodule
  firstCase : SourceFactorCase ρ first firstSpace
  secondCase : SourceFactorCase ρ second secondSpace

/-- B.5.6(5)'s second module, including its own central quotient in (b). -/
inductive HyperplaneSecondCase (B : Subgroup D) (U : Subrepresentation ρ) : Prop
  | linearThree (r : ℕ) (bound : r ≤ 2)
      (natural : IsRepeatedLinearNatural (U.toRepresentation.comp B.subtype)
        BinaryField.two 3 r)
  | linearTwo (F : BinaryField)
      (natural : IsLinearNatural (reducedAction (U.toRepresentation.comp B.subtype)) F 2)

/-- B.5.6(5) splits `[V,D]`; the supplement by `C_V(D)` has index two. -/
structure HyperplaneCase where
  first : Subgroup D
  second : Subgroup D
  product : InternalProduct first second
  firstEquiv : first ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
  firstDimension : Module.finrank (ZMod 2) (moved ρ first) = 3
  disjoint : Disjoint (moved ρ first) (moved ρ second)
  moved_eq : moved ρ ⊤ = moved ρ first ⊔ moved ρ second
  hyperplane : Module.finrank (ZMod 2) (V ⧸ (moved ρ ⊤ ⊔ ρ.invariants)) = 1
  secondSpace : Subrepresentation ρ
  secondSpace_eq : secondSpace.toSubmodule = moved ρ second
  secondCase : HyperplaneSecondCase ρ second secondSpace

/-- The nontrivial adequate alternatives; no module clause is dropped
outside the outer A₆–C₃ branch. -/
inductive NontrivialAdequateAlternative : Prop
  | quasisimple (quasisimple : IsQuasisimple (generalizedFitting D))
      (actions : ProjectiveLine.QuasisimpleSourceConclusion ρ (generalizedFitting D))
  | symmetricThree (case : SymmetricThreeCase ρ)
  | twoFactors (case : SourceTwoFactorCase ρ)
  | outerSixThree (case : OuterSixThreeShape D)
  | hyperplane (case : HyperplaneCase ρ)

/-- The separate adequate target, retaining the trivial actor admitted by B.5.3. -/
def AdequateAlternative : Prop := Subsingleton D ∨ NontrivialAdequateAlternative ρ

/-- A target universal implication, not an assumed earlier-source theorem. -/
def AdequateClassificationInput (K : GroupClass.{u}) : Prop :=
  ∀ (D : Type u) [Group D] [Finite D]
    (V : Type v) [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V), FFHypothesis K ρ → AdequateAlternative ρ

/-- Removing the degenerate branch uses actual nontriviality of the actor. -/
theorem AdequateAlternative.of_nontrivial [Nontrivial D] (h : AdequateAlternative ρ) :
    NontrivialAdequateAlternative ρ := by
  rcases h with h | h
  · exact (not_subsingleton D h).elim
  · exact h

/-- An actual nontrivial offender supplies the same specialization. -/
theorem AdequateAlternative.of_ff (h : AdequateAlternative ρ) (hff : IsFFModule ρ) :
    NontrivialAdequateAlternative ρ := by
  obtain ⟨A, hA⟩ := hff
  let : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr hA.1.1
  let : Nontrivial D := Function.Injective.nontrivial A.subtype_injective
  exact h.of_nontrivial ρ

end CFSG.Quasithin.ChapterB.SourceInduction
