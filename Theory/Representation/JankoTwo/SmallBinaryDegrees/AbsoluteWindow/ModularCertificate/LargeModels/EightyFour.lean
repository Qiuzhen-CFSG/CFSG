module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.Models
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.Presentation
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.Descent
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.Binary
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.EightyFour.Structure

/-!
# The degree-84 characteristic-two Hall--Janko action

The literal ATLAS J2G1-f2r84B0 generators satisfy the five presentation
relations. A kernel-checked rank-one polynomial, two orbit bases and their
inverses prove absolute irreducibility after interpretation in any
characteristic-two field. Injectivity of the presentation map descends this
action to the original degree-100 permutation carrier.

The only external input is that presentation injectivity. This module supplies
the degree-84 member of the modular-saturation family; it does not claim that
the family exhausts the simple modules. Source matrices and attribution:
LargeModels/source/README.md and ModularCertificate/Source.md.
-/

@[expose] public noncomputable section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.EightyFour
open Sporadic.LeechRelated.J2
open G2FourModule.Embedding.InnerRealization
open Binary
universe v

variable (F : Type v) [Field F] [CharP F 2]

/-- The actual degree-84 action of the literal degree-100 carrier. -/
def representation (hp : Function.Injective Presentation.toCarrier) :
    Representation F Carrier (Fin 84 → F) :=
  action hp (unitA F) (unitB F) (relations F)

@[simp] theorem representation_a (hp : Function.Injective Presentation.toCarrier) :
    representation F hp GeneratorPair.a = Matrix.toLin' (eval F 84 a) :=
  action_a hp (unitA F) (unitB F) (relations F)

@[simp] theorem representation_b (hp : Function.Injective Presentation.toCarrier) :
    representation F hp GeneratorPair.b = Matrix.toLin' (eval F 84 b) :=
  action_b hp (unitA F) (unitB F) (relations F)

theorem absolutelyIrreducible (hp : Function.Injective Presentation.toCarrier) :
    IsAbsolutelyIrreducible (representation F hp) := by
  let S := Algebra.adjoin F ({eval F 84 a, eval F 84 b} :
    Set (Matrix (Fin 84) (Fin 84) F))
  have ha : eval F 84 a ∈ S := Algebra.subset_adjoin (by simp)
  have hb : eval F 84 b ∈ S := Algebra.subset_adjoin (by simp)
  exact action_absolutelyIrreducible_of_rankOne hp (unitA F) (unitB F) (relations F)
    (vector F 84 column) (vector F 84 row)
    (eval F 84 p) (eval F 84 pi) (eval F 84 q) (eval F 84 qi)
    (rankOne_mem F S ha hb) (left_orbit F S ha hb) (right_orbit F S ha hb)
    (left_inverse F) (right_inverse F)

/-- The singleton degree-84 family required by modular saturation. -/
theorem modelsExist (hp : Function.Injective Presentation.toCarrier) :
    ModelsExist.{v} (fun _ : Fin 1 => 84) := by
  intro K _ _ _
  refine ⟨fun _ => representation K hp, ?_, ?_⟩
  · intro i
    let := absolutelyIrreducible K hp
    exact IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible _
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.EightyFour
