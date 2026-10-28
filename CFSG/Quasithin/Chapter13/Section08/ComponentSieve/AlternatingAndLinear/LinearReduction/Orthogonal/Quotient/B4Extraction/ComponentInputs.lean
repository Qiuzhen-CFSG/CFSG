module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.Quotient.Models
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Basic

/-!
# Explicit component-irreducible B.4 inputs

These are universal earlier-representation inputs, with faithfulness,
component irreducibility, the elementary quadratic actor and its ratio bound
all explicit. They are the L₄(2) and S₈ specializations of Aschbacher–Smith
B.4.2(9–10) and B.4.5, printed pp.86–87 (1 March 2004 manuscript).
They are definitions of hypotheses, not proofs of the earlier classification.

The S₈ input requires A₈-irreducibility. For a reducible restriction the L₄
input must instead be applied to a genuine irreducible constituent after
its faithfulness and actor bound have been proved. All model identifications
are equivariant and use the same specified markings.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalQuotient.B4Extraction
open Representation Representation.BinaryOffender
open FourStructure FourStructure.ChiefFactors
universe v
variable {H : Type*} [Group H]

/-- The orthogonal alternative on the marked component, expressed using the
actual eight-letter module, not its dimension. -/
def IsComponentOrthogonal {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (K : Subgroup H) (σ : Representation (ZMod 2) K E)
    (eH : H ≃* Equiv.Perm (Fin 8)) : Prop :=
  ∃ e : E ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8),
    ∀ k : K, ∀ v, e (σ k v) =
      BinaryPermutation.naturalRepresentation (Fin 8) (eH k) (e v)

/-- Universal component-irreducible specialization of B.4.2 and B.4.5 to
L₄(2). This is an explicit earlier-theorem input, not a proved classification.
Both markings must be the fixed compatible markings of the source application.
The natural and dual models use eK; the orthogonal model uses eH. -/
def ComponentB4 (K : Subgroup H) (eH : H ≃* Equiv.Perm (Fin 8))
    (eK : K ≃* BinaryLinear.GL FourSpace) : Prop :=
  ∀ (E : Type v) [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] (σ : Representation (ZMod 2) K E),
    Function.Injective σ → IsIrreducible σ →
    ∀ A : Subgroup K, IsElementaryTwo A → IsQuadratic σ A →
      fixedCodim σ A ≤ 2 * rank A →
      IsNaturalOrDual σ eK ∨ IsComponentOrthogonal K σ eH

/-- Universal S₈ specialization of B.4, retaining its component-irreducibility
hypothesis. It cannot be used merely from irreducibility of the S₈ action. -/
def SymmetricB4 (K : Subgroup H) (eH : H ≃* Equiv.Perm (Fin 8)) : Prop :=
  ∀ (E : Type v) [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] (σ : Representation (ZMod 2) H E),
    Function.Injective σ → IsIrreducible (σ.comp K.subtype) →
    ∀ A : Subgroup H, IsElementaryTwo A → IsQuadratic σ A →
      fixedCodim σ A ≤ 2 * rank A → IsEightNatural σ eH

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalQuotient.B4Extraction
