module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.Models
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.Descent
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.Presentation
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour.Trace
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour.Orbits
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.Parameters

/-!
# The two degree-64 Hall--Janko actions in characteristic two

The original ATLAS generators satisfy all five presentation relations. A checked
rank-one element with two invertible orbit bases proves full matrix-algebra
span, hence absolute irreducibility. Evaluating the F₄ coefficients at t and t²
constructs two actions of the literal degree-100 carrier. The original signed
trace word has traces t and t², which are unequal, proving inequivalence.

The only earlier premise is injectivity of the fixed presentation map onto the
carrier. Matrix relations, density, coefficient transport and trace separation
are conclusions. The sources, conventions and measured kernel checks are
recorded in `SixtyFour/source/README.md` and `LargeModels/source/README.md`.
-/

@[expose] public noncomputable section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour
open Sporadic.LeechRelated.J2 G2FourModule.Embedding.InnerRealization
universe v
variable {F : Type*} [Field F] [CharP F 2]

def unitA (t : F) (ht : t ^ 2 = t + 1) : (Matrix (Fin 64) (Fin 64) F)ˣ :=
  SmallModels.unitA (Packed.eval t 64 Data.A) (Packed.eval t 64 Data.B)
    (Relations.matrix_relations t ht)

def unitB (t : F) (ht : t ^ 2 = t + 1) : (Matrix (Fin 64) (Fin 64) F)ˣ :=
  SmallModels.unitB (Packed.eval t 64 Data.A) (Packed.eval t 64 Data.B)
    (Relations.matrix_relations t ht)

theorem unit_relations (t : F) (ht : t ^ 2 = t + 1) :
    Presentation.Relations (unitA t ht) (unitB t ht) :=
  SmallModels.units_relations _ _ (Relations.matrix_relations t ht)

/-- The second pair is obtained by coefficient Frobenius on the actual
generator matrices used by the two carrier actions. -/
theorem generators_frobenius (t : F) (ht : t ^ 2 = t + 1) :
    (unitA (t ^ 2) (SmallModels.square_parameter t ht) : Matrix (Fin 64) (Fin 64) F) =
      (unitA t ht : Matrix (Fin 64) (Fin 64) F).map (frobenius F 2) ∧
    (unitB (t ^ 2) (SmallModels.square_parameter t ht) : Matrix (Fin 64) (Fin 64) F) =
      (unitB t ht : Matrix (Fin 64) (Fin 64) F).map (frobenius F 2) :=
  ⟨Packed.eval_frobenius t 64 Data.A, Packed.eval_frobenius t 64 Data.B⟩

/-- The trace witness is the original signed word on the presentation generators. -/
def traceElement : Presentation.UniversalGroup :=
  Words.signed (PresentedGroup.of 0) (PresentedGroup.of 1) Data.traceWord

theorem unit_trace (t : F) (ht : t ^ 2 = t + 1) :
    Matrix.trace (Presentation.toGroup (unitA t ht) (unitB t ht)
      (unit_relations t ht) traceElement : Matrix (Fin 64) (Fin 64) F) = t := by
  have hw : (Presentation.toGroup (unitA t ht) (unitB t ht)
      (unit_relations t ht) traceElement : Matrix (Fin 64) (Fin 64) F) =
      Words.matrixWord (Packed.eval t 64 Data.A) (Packed.eval t 64 Data.B) Data.traceWord := by
    rw [traceElement, Words.map_signed, Presentation.toGroup_zero, Presentation.toGroup_one]
    exact Words.coe_signed_units _ _ (Relations.matrix_relations t ht) Data.traceWord
  rw [hw]
  exact Trace.trace_word t ht

def representation (hp : Function.Injective Presentation.toCarrier)
    (t : F) (ht : t ^ 2 = t + 1) : Representation F Carrier (Fin 64 → F) :=
  action hp (unitA t ht) (unitB t ht) (unit_relations t ht)

theorem representation_irreducible (hp : Function.Injective Presentation.toCarrier)
    (t : F) (ht : t ^ 2 = t + 1) : IsIrreducible (representation hp t ht) :=
  action_irreducible hp _ _ _ (Orbits.density t ht)

theorem representation_absolutelyIrreducible (hp : Function.Injective Presentation.toCarrier)
    (t : F) (ht : t ^ 2 = t + 1) : IsAbsolutelyIrreducible (representation hp t ht) :=
  action_absolutelyIrreducible hp _ _ _ (Orbits.density t ht)

theorem representations_inequivalent (hp : Function.Injective Presentation.toCarrier)
    (t : F) (ht : t ^ 2 = t + 1) :
    IsEmpty ((representation hp t ht).Equiv
      (representation hp (t ^ 2) (SmallModels.square_parameter t ht))) := by
  apply actions_inequivalent_of_trace hp _ _ _ _ _ _ traceElement
  rw [unit_trace, unit_trace]
  exact (SmallModels.square_ne_self t ht).symm

/-- Both actual simple actions, in every field universe, with no matrix or
irreducibility premise. Presentation injectivity is discharged upstream. -/
theorem modelsExist (hp : Function.Injective Presentation.toCarrier) :
    ModelsExist.{v} (fun _ : Fin 2 => 64) := by
  intro F _ _ _
  obtain ⟨t, ht⟩ := SmallModels.exists_parameter (F := F)
  let ρ := representation hp t ht
  let σ := representation hp (t ^ 2) (SmallModels.square_parameter t ht)
  have hρ : IsIrreducible ρ := representation_irreducible hp t ht
  have hσ : IsIrreducible σ := representation_irreducible hp _ _
  have hne : IsEmpty (ρ.Equiv σ) := representations_inequivalent hp t ht
  refine ⟨![ρ, σ], ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hρ
    · exact hσ
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hne
    · exact ⟨fun e => hne.false e.symm⟩
    · exact (hij rfl).elim

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour
