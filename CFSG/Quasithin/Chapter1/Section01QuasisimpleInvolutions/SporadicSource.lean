module

public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.SporadicReduction
public import Theory.SpecificGroups.Rudvalis.Model.OuterStabilizer

/-!
# The source Rudvalis branch of the marked involution classification

The actual central-quotient equivalence supplies simplicity of the Rudvalis
carrier. The proved point-stabilizer theorem then realizes the original quotient
automorphism and the checked normalizer calculation forces it to be inner.
Perfect central lifting preserves the original marked automorphism upstairs.
Thus no automorphism-realization premise remains in the Rudvalis alternative.

Source: Aschbacher--Smith 1.1.5(3)(f), printed p.503.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
open Chapter15.Section03.Candidates.ComponentStructure
variable {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
  {α : MulAut L} {P : Sylow 2 L}

/-- The complete Rudvalis alternative on the original group and action. -/
theorem MarkedInvolution.modelAction_ru (d : MarkedInvolution α P)
    (e : L ⧸ center L ≃* Rudvalis.Model) : ModelAction115 L α := by
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : IsSimpleGroup Rudvalis.Model := e.symm.isSimpleGroup
  exact d.modelAction_ru_of_stabilizers e Rudvalis.outer_stabilizer_map_eq

end CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
