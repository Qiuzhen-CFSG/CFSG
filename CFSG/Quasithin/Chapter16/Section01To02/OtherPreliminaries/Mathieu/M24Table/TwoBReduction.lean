module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Mathieu.M24Table
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoB.Reduction

/-!
# The class-2B geometric inputs in the M₂₄ involution table

The full marked 2B centralizer has the required E₆₄ extension and component
exclusion once the full-weight translation centralizer is placed in its
sextet stabilizer and its actual vector stabilizer is identified with S₅.
The 2A calculation remains independent. These are conditional applications,
not an unconditional proof of Aschbacher–Smith 16.1.5(7), printed p.1171.
-/

public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.Mathieu
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M24InvolutionCentralizers
open M24LocalGeometry Theory.GroupTheory

theorem m24_involution_alternative_of_twoB_geometry
    (hA : IsM24DihedralExtension centralizer2A)
    (hplace : TwoB.nativeCentralizer ≤ sextetStabilizer standardSextet)
    (q : TwoB.actors ≃* S5)
    (r : MulAut M24) (hr : orderOf r = 2) : M24InvolutionAlternative r :=
  m24_involution_alternative_of_representatives hA
    ⟨TwoB.extensionOfGeometry hplace q⟩ r hr

theorem m24_no_component_of_twoB_geometry
    (hA : ∃ Q : Subgroup centralizer2A,
      Q.Normal ∧ IsPGroup 2 Q ∧ centralizer (Q : Set centralizer2A) ≤ Q)
    (hplace : TwoB.nativeCentralizer ≤ sextetStabilizer standardSextet)
    (r : MulAut M24) (hr : orderOf r = 2) (K : Subgroup r.fixedSubgroup) :
    ¬ IsComponent r.fixedSubgroup K :=
  m24_no_component_of_representative_kernels hA
    (TwoB.exists_normal_selfCentralizing_two_subgroup hplace) r hr K

end CFSG.Quasithin.Chapter16.OtherPreliminaries.Mathieu
