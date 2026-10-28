module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.Classes
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.Table

/-!
# Separate representation-theoretic obligations for the normalizer table

The first seven rows are to be obtained by inflation from the actual A6
quotient. The last five are to be obtained from the inertia subgroup of a
nonprincipal character of E. Each contract asks for genuine irreducible
representation characters and their values on the marked representatives.
Neither contract assumes cancellation or the desired normalizer record.

These are conditional interfaces. Their inhabitants, as well as actual class
coverage, must be constructed before the source character theorem is complete.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 6, pp.10–11.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] {D : LocalData G}
    {k : TwistedModel ≃* D.centralizer}

/-- The seven actual quotient characters, with the two fifth-order values
encoded by the roots of `X²-X-1`. The principal character is row zero. -/
public structure NormalizerInflatedBlock (Q : NormalizerClassData D k) where
  parameter : ℂ
  parameter_equation : parameter ^ 2 = parameter + 1
  character : Fin 7 → ClassFunction (normalizer (CaseII.E D k : Set G))
  irreducible : ∀ j, IsIrreducibleCharacter (character j)
  principal : character 0 = 1
  values : ∀ j r, character j (Q.representative r) =
    normalizerFullValues parameter (Fin.castAdd 5 j) r

/-- The five actual noninflated irreducibles. Their table entries are all
integral and independent of the fifth-root parameter. -/
public structure NormalizerInducedBlock (Q : NormalizerClassData D k) where
  character : Fin 5 → ClassFunction (normalizer (CaseII.E D k : Set G))
  irreducible : ∀ j, IsIrreducibleCharacter (character j)
  values : ∀ j r, character j (Q.representative r) =
    normalizerFullValues 0 (Fin.natAdd 7 j) r

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
