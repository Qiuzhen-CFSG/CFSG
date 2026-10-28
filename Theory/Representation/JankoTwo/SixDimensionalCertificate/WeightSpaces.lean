module

public import Theory.Representation.JankoTwo.SixDimensionalCertificate.Weights
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.TraceGeometry.Generators
public import Mathlib.RepresentationTheory.Character
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Applying the finite weight certificate to the literal J₂ action

The multiplicities below are dimensions of intersections of eigenspaces for
the two specified carrier elements. Rotation invariance, the dimension sum,
and nontriviality reduce these actual multiplicities to four possibilities.
These three inputs still require the spectral decomposition argument; this
module does not assert the degree-six classification.

The outer witness has the same character effect as the prescribed
`involutionAut`, because its additional factor is inner. This retains the
literal automorphism in the eventual trace comparison.

Source application: Aschbacher--Smith K.4.5, printed p.460; Hiss--Malle,
corrected Table 2, the characteristic-two degree-six J₂ entry.
-/

@[expose] public noncomputable section
namespace Representation.JankoTwo.SixDimensionalCertificate
open Sporadic.LeechRelated.J2
open scoped BigOperators

variable {E U : Type*} [Field E] [AddCommGroup U] [Module E U]

/-- Simultaneous eigenvalue multiplicities of the literal order-five pair. -/
def weightMultiplicity (ρ : Representation E Carrier U) (ζ : E) (w : Weights.Weight) : ℕ :=
  Module.finrank E ((Module.End.eigenspace (ρ TraceGeometry.x) (ζ ^ w.1.val) ⊓
    Module.End.eigenspace (ρ TraceGeometry.y) (ζ ^ w.2.val)) : Submodule E U)

/-- The finite calculation applied to actual eigenspaces, conditional on the
three spectral-decomposition inputs, rather than on a representation catalogue. -/
theorem four_patterns_of_weight_decomposition (ρ : Representation E Carrier U) (ζ : E)
    (hrotation : ∀ w, weightMultiplicity ρ ζ (Weights.rotate w) = weightMultiplicity ρ ζ w)
    (hdegree : ∑ w, weightMultiplicity ρ ζ w = 6)
    (hnontrivial : weightMultiplicity ρ ζ 0 < 6) :
    ∃ i : Fin 4, ∀ w, weightMultiplicity ρ ζ w = Weights.pattern i w := by
  obtain ⟨i, hi⟩ := Weights.four_patterns (weightMultiplicity ρ ζ)
    hrotation hdegree hnontrivial
  exact ⟨i, fun w => congrFun hi w⟩

private theorem character_comp_conj (ρ : Representation E Carrier U)
    (q : Carrier) (α : MulAut Carrier) :
    Representation.character (ρ.comp (MulAut.conj q * α).toMonoidHom) =
      Representation.character (ρ.comp α.toMonoidHom) := by
  funext g
  exact ρ.char_conj (α g) q

/-- The finite outer-normalizer witness induces exactly the prescribed
outer twist on characters. -/
theorem outerTwist_character [FiniteDimensional E U] (ρ : Representation E Carrier U) :
    Representation.character (ρ.comp TraceGeometry.outerTwist.toMonoidHom) =
      Representation.character (ρ.comp ExceptionalParabolics.involutionAut.toMonoidHom) := by
  exact character_comp_conj ρ TraceGeometry.k ExceptionalParabolics.involutionAut

end Representation.JankoTwo.SixDimensionalCertificate
