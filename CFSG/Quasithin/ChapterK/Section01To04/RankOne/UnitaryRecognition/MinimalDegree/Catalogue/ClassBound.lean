module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.MinimalDegree.Catalogue.Assembly
public import Theory.SpecificGroups.SU3.BinaryPRegularClasses

/-!
# The unitary class-counting route to the Schur word model

The trace bound supplies the exact `hclasses` premise of the finite-family
assembly for the literal SU₃ Schur model. Restricted-word simplicity and
separation remain explicit; their independent producer is
`qt-k03-unitary-word-restriction`.

The class bound now discharges both matrix correction premises over the
specified quadratic finite field. The earlier conditional interface is
retained, while `exists_schur_word_model_of_simple_family` needs only the
independent restricted-word simplicity and separation. The full word
catalogue remains with `qt-k03-unitary-word-catalogue`.

Sources: GLS III, 2.8.2, 2.8.6(a), and the four factors of 2.8.10(c),
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section

open BenderSuzuki.MatrixGroups Representation Matrix
open Representation.SL3.BinaryDefiningFactors
open scoped MonoidAlgebra TensorProduct

namespace CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.MinimalDegree

variable {F K : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
  [Field K] [IsAlgClosed K] [CharP K 2]

/-- Apply the trace class bound to the actual extended Schur model. This
discharges the class-cardinality premise from the two matrix correction inputs,
while retaining the independent restricted-word simplicity and separation. -/
theorem exists_schur_word_model_of_simple_family_and_unitary_corrections
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (J : HermitianForm 3 F)
    (σ : Representation (ZMod 2) J.specialSubgroup V) [IsIrreducible σ]
    [Algebra (Module.End (ZMod 2)[J.specialSubgroup] σ.asModule) K]
    (s : ℕ) (ι : F →+* K) (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hirr : ∀ w : List Factor, w.length = s → IsIrreducible (word J ι w))
    (hne : ∀ v w : List Factor, v.length = s → w.length = s →
      Nonempty ((word J ι v).Equiv (word J ι w)) → v = w)
    (hunitary : ∀ g h : J.specialSubgroup,
      ¬ 2 ∣ orderOf g → ¬ 2 ∣ orderOf h →
      ∀ D : GL (Fin 3) F, D * g.val = h.val * D →
        ∃ U : J.unitarySubgroup, U.val * g.val = h.val * U.val)
    (hdet : ∀ g : J.specialSubgroup, ¬ 2 ∣ orderOf g →
      ∀ d : Fˣ, J.conj (d : F) * (d : F) = 1 →
        ∃ C : J.unitarySubgroup, Commute C.val g.val ∧ GeneralLinearGroup.det C.val = d) :
    ∃ w : List Factor, w.length = s ∧
      Nonempty ((extendScalars K σ.endFieldRep).Equiv (word J ι w)) := by
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  exact exists_schur_word_model_of_simple_family_and_class_bound
    J σ s ι hcard hirr hne
    (Theory.SpecificGroups.SU3.BinaryPRegularClasses.card_pRegularConjClasses_le_of_unitary_corrections
      J hunitary hdet)

/-- Apply the proved odd-order class bound to the literal extended Schur model.
Only restricted-word simplicity and separation remain as representation-theoretic
inputs; both unitary matrix corrections and the class bound are discharged. -/
theorem exists_schur_word_model_of_simple_family
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (J : HermitianForm 3 F)
    (σ : Representation (ZMod 2) J.specialSubgroup V) [IsIrreducible σ]
    [Algebra (Module.End (ZMod 2)[J.specialSubgroup] σ.asModule) K]
    (s : ℕ) (hs : 2 ≤ s) (ι : F →+* K)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (hirr : ∀ w : List Factor, w.length = s → IsIrreducible (word J ι w))
    (hne : ∀ v w : List Factor, v.length = s → w.length = s →
      Nonempty ((word J ι v).Equiv (word J ι w)) → v = w) :
    ∃ w : List Factor, w.length = s ∧
      Nonempty ((extendScalars K σ.endFieldRep).Equiv (word J ι w)) := by
  exact exists_schur_word_model_of_simple_family_and_class_bound
    J σ s ι hcard hirr hne
    (Theory.SpecificGroups.SU3.BinaryPRegularClasses.card_pRegularConjClasses_le
      J s hs hcard hconj)

end CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.MinimalDegree
