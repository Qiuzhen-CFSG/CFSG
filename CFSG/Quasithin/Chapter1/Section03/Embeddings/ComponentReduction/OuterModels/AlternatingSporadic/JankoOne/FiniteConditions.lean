module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne.MatrixData
public import Theory.SpecificGroups.Janko1.Model.Certification.Order.Generators

/-!
# The finite checks for the J₁ automorphism calculation

The orbit calculation has two independent parts: closure of the literal matrix
family under the two conjugations, and identification of every member satisfying
the seventh- and nineteenth-power relations with a conjugate of `a` by an element
centralizing `b`. These conditions concern explicit matrices and actual model
elements. They do not postulate anything about automorphism groups.

`Reduction` proves that supplying both conditions makes every automorphism
inner. Neither condition is assumed proved by this module. The target is the
`Out(J₁) = 1` entry of GLS3, Table 5.3f, as used on Aschbacher–Smith p.510.
-/

namespace Janko1.OuterCertificate
open OrderCertificate

/-- The two finite matrix-closure obligations. -/
@[expose] public def OrbitClosed : Prop :=
  (∀ i : Fin 1463, ∃ j : Fin 1463,
    matrixA * orbitMatrix i * matrixA = orbitMatrix j) ∧
  (∀ i : Fin 1463, ∃ j : Fin 1463,
    matrixB * orbitMatrix i * (matrixB * matrixB) = orbitMatrix j)

/-- The finite generator-image calculation after fixing the order-three generator. -/
@[expose] public def GeneratorImageRigid : Prop :=
  ∀ i : Fin 1463,
    (orbitMatrix i * matrixB) ^ 7 = 1 →
    (orbitMatrix i * matrixB * orbitMatrix i * matrixB ^ 2) ^ 19 = 1 →
    ∃ g : Model, matrixValue (g * a * g⁻¹) = orbitMatrix i ∧ g * b * g⁻¹ = b

end Janko1.OuterCertificate
