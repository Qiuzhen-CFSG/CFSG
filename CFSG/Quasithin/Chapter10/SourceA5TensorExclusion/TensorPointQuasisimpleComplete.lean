module

public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointQuasisimpleReduction
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointQuasisimpleJankoFour

/-!
# The original tensor point component is not quasisimple

The full source-C catalogue applies to the literal central quotient of a
quasisimple point component. The tensor action and its central involution
exclude the Lie-type and alternating rows and the smaller sporadic rows.
The actual residual and moved module descend to the same central quotient,
where the completed local catalogues exclude Held and Janko four.

This proves the quasisimple exclusion in Aschbacher--Smith 9.4.1, printed
p.735, under the original point-centralizer containment and normalization
hypotheses, without a quotient shortlist or model-fact callback.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- A point-centralizer subgroup containing the original tensor residual
and normalized by the point centralizer cannot be quasisimple. -/
theorem tensorPoint_containing_not_quasisimple (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} (hLI : m.tensorPointResidual v ≤ I)
    (hIX : I ≤ centralizer ({(v : G)} : Set G))
    (hIN : centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G)) :
    ¬ IsQuasisimple I := by
  intro hI
  let := hI
  obtain ⟨a⟩ := m.tensorPoint_containing_quasisimple_janko4 v hv hLI hIX hIN
  exact m.tensorPoint_containing_not_janko4 v hv hLI hIX hIN a

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
