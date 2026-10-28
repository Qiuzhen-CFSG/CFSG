module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Centralizer.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Centralizer.ResidualLocal.Transport
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Centralizer.ResidualLocal.ModelFacts
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Centralizer.ResidualLocal.TransferApplication

/-!
# Residual facts for the second involution centralizer

The central Sylow subgroup in the marked eight-point model supplies fusion
control in K ∩ L. Exact two-residual transfer then gives J ∩ L = X, retaining
both literal inclusions in the definition of X. The supported A₄ model
supplies its order, marked involution, involution conjugacy and four-group
centralizer. Transport assembles all five fields of `ResidualFacts`, and
the existing recognition theorem identifies J with A₅ when K is not in L.

All model and transfer premises are discharged here. In particular the
intersection uses the full residual restriction theorem, whose lower central
series argument strengthens the abelian transfer calculation for O²(K)[K,K].
Once `InvolutionData` is supplied, the residual facts need only the involution
and full-centralizer hypotheses; the source wrappers also accept the original
nonnormal-quaternion, intersection and thirteen-element fusion inputs.

Source: Aschbacher, “A 2-local characterization of M12”, Proposition 3.3,
printed p.38. The extension to the whole second centralizer remains with the
parent `Centralizer` assembly.
-/

namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index
open Subgroup
variable {G : Type*} [Group G] [Finite G] {z : G}

namespace InvolutionData
variable {L : Subgroup G} (d : InvolutionData z L)

/-- Exact transfer for the source local subgroup, with the central Sylow
premise discharged by the marked eight-point model. -/
public theorem residual_intersection (hz : orderOf z = 2) (hCL : Centralizer z ≤ L) :
    d.J ⊓ L = d.X :=
  d.intersection_of_model_central_sylow hz hCL ResidualModel.exists_central_sylow

/-- All source residual facts, with no residual, transfer or model premise. -/
public theorem residualFacts (hz : orderOf z = 2) (hCL : Centralizer z ≤ L) :
    ResidualFacts d :=
  d.residualFacts_of_intersection hz hCL (d.residual_intersection hz hCL)

end InvolutionData

/-- The residual contract under the original source inputs. The earlier
geometric hypotheses are already encoded in the supplied marked subgroup. -/
public theorem residualFacts_of_source (h : Hypotheses z)
    (_hn : QuaternionSubgroupsNonnormal z)
    (_local_intersections : ∀ g : G, g * z * g⁻¹ ∈ coreInG z → g * z * g⁻¹ ≠ z →
      IntersectionData z g)
    (_h13 : Nat.card (CoreFusion z) = 13)
    (L : Subgroup G) (hCL : Centralizer z ≤ L) (d : InvolutionData z L)
    (_hK : ¬ d.K ≤ L) : ResidualFacts d :=
  d.residualFacts h.involution hCL

/-- The actual A₅-recognition consumer under the original source inputs,
with every field of its residual contract proved. -/
public theorem residual_equiv_alternating_five_of_source (h : Hypotheses z)
    (hn : QuaternionSubgroupsNonnormal z)
    (local_intersections : ∀ g : G, g * z * g⁻¹ ∈ coreInG z → g * z * g⁻¹ ≠ z →
      IntersectionData z g)
    (h13 : Nat.card (CoreFusion z) = 13)
    (L : Subgroup G) (hCL : Centralizer z ≤ L) (d : InvolutionData z L)
    (hK : ¬ d.K ≤ L) : Nonempty (d.J ≃* alternatingGroup (Fin 5)) :=
  residual_equiv_alternating_five d h.involution hCL hK
    (residualFacts_of_source h hn local_intersections h13 L hCL d hK)

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index
