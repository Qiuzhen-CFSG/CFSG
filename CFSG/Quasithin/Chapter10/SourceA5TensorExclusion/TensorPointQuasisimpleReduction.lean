module

public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointQuasisimpleModels
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointQuasisimpleLocal

/-!
# The final quotient row in the tensor quasisimple branch

The full source C catalogue reduces the original component to Held or J₄.
The actual point residual survives the central quotient as a Sylow-normalized
local A₅ component with nontrivial two-core. Held's proved local catalogue
excludes that configuration. Thus only the literal J₄ quotient remains for
the separate final local exclusion.

Source: Aschbacher--Smith 9.4.1, printed p.735, using A.2.4 and A.3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The full quotient inspection and the original Held local exclusion leave J₄. -/
theorem tensorPoint_containing_quasisimple_janko4 (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} [IsQuasisimple I]
    (hLI : m.tensorPointResidual v ≤ I)
    (hIX : I ≤ centralizer ({(v : G)} : Set G))
    (hIN : centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G)) :
    Nonempty ((I ⧸ center I) ≃* Janko4.Model) := by
  rcases m.tensorPoint_containing_quasisimple_held_or_janko4 v hv hLI hIX hIN with hH | hJ
  · exact (m.tensorPoint_containing_not_held v hv hLI hIX hIN hH.some).elim
  · exact hJ

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
