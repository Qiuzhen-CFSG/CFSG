module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Centralizer.ResidualLocal.ModelDefinitions
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Centralizer.ResidualLocal.Transport
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Centralizer.ResidualLocal.ModelFacts.Residual

/-!
# The marked eight-point residual facts and their consumers

The local centralizer has a Sylow two-subgroup centralized by the mark `z8`.
Its two-residual is the actual A₄ on the last four points; it contains `i8`,
has one involution class, and the centralizer of `i8` is a Klein four-group.
The concrete facts discharge the model premises of local fusion and residual
recognition. The ambient transfer equality `J ∩ L = X` is retained explicitly:
its proof belongs to the source-theorem assembly, not the finite model.

Source: Aschbacher, “A 2-local characterization of M12”, Proposition 3.3,
printed p.38.
-/

public section
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index
open Subgroup
namespace InvolutionData
variable {G : Type*} [Group G] [Finite G] {z : G} {L : Subgroup G}
  (d : InvolutionData z L)

/-- The concrete central Sylow subgroup discharges the model premise of fusion. -/
theorem local_two_element_fusion_of_eight_model
    (hz : orderOf z = 2) (hCL : Centralizer z ≤ L)
    {a b : d.K} (ha : a ∈ d.M) (hb : b ∈ d.M)
    (hap : IsPGroup 2 (zpowers a)) (hab : IsConj a b) :
    ∃ m ∈ d.M, m * a * m⁻¹ = b :=
  d.local_two_element_fusion hz hCL ResidualModel.exists_central_sylow ha hb hap hab

/-- All finite-model premises are discharged; only ambient transfer remains. -/
theorem residualFacts_of_intersection
    (hz : orderOf z = 2) (hCL : Centralizer z ≤ L)
    (htransfer : d.J ⊓ L = d.X) : ResidualFacts d :=
  d.residualFacts_of_model_and_intersection hz hCL htransfer
    ResidualModel.R_card ResidualModel.i_mem ResidualModel.R_involution_fusion
    ResidualModel.R_centralizer_equiv

/-- The source's A₅ recognition, with the ambient transfer equality explicit. -/
theorem residual_equiv_alternating_five_of_intersection
    (hz : orderOf z = 2) (hCL : Centralizer z ≤ L) (hK : ¬ d.K ≤ L)
    (htransfer : d.J ⊓ L = d.X) : Nonempty (d.J ≃* alternatingGroup (Fin 5)) :=
  residual_equiv_alternating_five d hz hCL hK
    (d.residualFacts_of_intersection hz hCL htransfer)

end InvolutionData
end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index
end
