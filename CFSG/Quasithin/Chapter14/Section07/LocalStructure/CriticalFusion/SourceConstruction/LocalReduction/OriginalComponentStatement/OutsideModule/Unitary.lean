module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideModule.Multiplicity
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.MultiplicitySections

/-!
# The outside even-degree unitary module obstruction

A normal cubic and its component-centralizing inverter give an actual
faithful multiplicity representation. The quadratic actor yields an FF
offender on that representation, whose generalized Fitting subgroup is the
original component. The native irreducible-section classification then
excludes an even-degree projective unitary component.

All hypotheses refer to the actual finite group and its binary module.
No Chapter13 source context or assumed FF-module exclusion is used.
Source: Aschbacher–Smith, 14.7.42–43, printed pp.1061–1062, using
13.8.20(a) and B.4.2, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory InvertedCubicTensor
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideModule
open Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections
universe u
variable {D W : Type u} [Group D] [Finite D]
  [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

/-- The concrete quadratic actor rules out an even-degree unitary component. -/
theorem outside_even_unitary_false
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (K X : Subgroup D) [K.Normal] [X.Normal] [IsQuasisimple K]
    (hx : Nat.card X = 3)
    (hcommon : centralizer (K : Set D) ⊓ centralizer (X : Set D) ≤ X)
    (s : S₃ →* D) (hs : ∀ (k : K) t, Commute (k : D) (s t))
    (hmark : (alternatingGroup (Fin 3)).map s = X)
    (hg : subspaceCommutator ρ ⊤ X = ⊤)
    (A : Subgroup D) (hA : IsElementaryTwo A) (hquad : IsQuadratic ρ A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hz : center K = ⊥) (hS : IsSQTK KnownSimple.IsKnownSimple D)
    {Q : Type*} [Field Q] [Finite Q]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 Q)
    {n : ℕ} (hn : 0 < n) (heven : Even n) (hQ : Nat.card Q = 2 ^ (2*n))
    (hconj : ∀ x, J.conj x = x ^ (2^n))
    (e : K ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :
    False := by
  obtain ⟨hsE,hfaith,hoff,hfit⟩ := faithful_ff_multiplicity
    ρ hf K X hx hcommon s hs hmark hg A hA hquad hbound
  let μ := multiplicity (ρ.comp s) (ρ.comp (K ⊔ A : Subgroup D).subtype)
    (ambient_commute ρ (K ⊔ A : Subgroup D).subtype s hsE)
  have hFF : IsFFModule μ := ⟨A.subgroupOf (K ⊔ A),hoff⟩
  exact unitary_not_ff_of_generated_fitting K A μ hfaith hfit hz
    (hS.subgroup (K ⊔ A)) J hn heven hQ hconj e hFF

/-- The outside configuration excludes the packaged even-degree PSU₃ row. -/
theorem no_even_unitary
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (K X : Subgroup D) [K.Normal] [X.Normal] [IsQuasisimple K]
    (hx : Nat.card X = 3)
    (hcommon : centralizer (K : Set D) ⊓ centralizer (X : Set D) ≤ X)
    (s : S₃ →* D) (hs : ∀ (k : K) t, Commute (k : D) (s t))
    (hmark : (alternatingGroup (Fin 3)).map s = X)
    (hg : subspaceCommutator ρ ⊤ X = ⊤)
    (A : Subgroup D) (hA : IsElementaryTwo A) (hquad : IsQuadratic ρ A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hz : center K = ⊥) (hS : IsSQTK KnownSimple.IsKnownSimple D)
    (n : ℕ) (hn : 2 ≤ n) (heven : Even n) :
    ¬ ClassicalGroup.IsPSU K 3 (2^n) := by
  rintro ⟨Q,hQf,hQfin,J,hQ,hconj,⟨e⟩⟩
  exact outside_even_unitary_false ρ hf K X hx hcommon s hs hmark hg A hA
    hquad hbound hz hS J (by omega) heven
    (by simpa only [pow_mul,Nat.mul_comm] using hQ) hconj e

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideModule
