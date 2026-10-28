module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoCartanG2Natural

/-!
# The original linear and G₂ tensor rows

The actual Cartan factor orbits exclude the linear-three action images.
The original central involution survives the moved/fixed quotient, supplies
the G₂ natural fixed vector and selects the original long local component.
The resulting Cartan centralization contradicts the Hall cubic in the old
residual. Thus both exclusions hold on the same generation-two overgroup
and the literal Omega action quotient.

The final application removes the row-exclusion premise from the tensor
assembly. Its earlier Cartan/amalgam and symplectic-plane premises remain
with the final tensor owner, qt-d-tensor-exclusion.
Source: Aschbacher--Smith 9.3.8--9, printed p.734.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The two original action rows are excluded without any extra geometric premise. -/
theorem linearAndG2Exclusion : m.LinearAndG2Exclusion :=
  m.linearAndG2Exclusion_of_cartan_and_fixedVector (fun c => c.cartanOrbits) m.g2FixedVectorInput

/-- The original tensor consumer with its linear and G₂ premise discharged. -/
theorem false_of_generationTwo_cartan_inputs
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal)
    (hnormal : m.NonzeroCoreCartanNormalization)
    (hzero : m.ZeroCoreLineCentralization) (hcontain : A5PairContainment G)
    (hplane : m.SymplecticPlaneRecognition) : False :=
  m.false_of_generationTwo_source_inputs hout hnormal hzero hcontain m.linearAndG2Exclusion hplane

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
