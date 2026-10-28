module

public import Theory.GroupTheory.PResidual.FusionControl
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Centralizer.ResidualLocal.Transport

/-!
# The second-centralizer residual intersection

The concrete model's central Sylow premise supplies two-element fusion control
in K ∩ L. Its already proved odd index then gives the exact restriction of
O²(K), and the literal inclusion maps identify this with J ∩ L = X in G.
This discharges the transfer premise of `intersection_of_residual_restriction`;
the model Sylow premise remains with the enclosing source assembly.

Source: Aschbacher, “A 2-local characterization of M12”, Proposition 3.3,
printed p.38, https://authors.library.caltech.edu/records/m3wrn-5w840/files/ASCijm03.pdf.
-/

namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index
namespace InvolutionData

/-- The source residual intersection, conditional only on the marked central Sylow model fact. -/
public theorem intersection_of_model_central_sylow
    {G : Type*} [Group G] [Finite G] {z : G} {L : Subgroup G}
    (d : InvolutionData z L) (hz : orderOf z = 2) (hCL : Centralizer z ≤ L)
    (hmodel : ∃ T : Sylow 2 ResidualModel.C,
      ResidualModel.z ∈ (T : Subgroup ResidualModel.C) ∧
      ∀ a ∈ (T : Subgroup ResidualModel.C), Commute ResidualModel.z a) :
    d.J ⊓ L = d.X := by
  apply d.intersection_of_residual_restriction
  exact Subgroup.twoResidual_inf_eq_of_odd_index_fusion d.M (d.local_index_odd hz hCL)
    (fun _ _ ha hb hp hab => d.local_two_element_fusion hz hCL hmodel ha hb hp hab)

end InvolutionData
end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index
