module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Mathieu.M24Table
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoA.Quotient

/-!
# Component exclusion for the marked M24 2A centralizer

The specified binary point-radical preimage in the literal 2A centralizer
is a normal self-centralizing two-group. It discharges the first kernel-action
premise of the M24 table and excludes every component of this representative.
The actual quotient by this same kernel is PSL3(2). Thus only the embedded
dihedral-factor calculation remains for its source-table shape. The other
representative is a separate calculation.

Source: Aschbacher–Smith 16.1.5(7) and 16.1.7, printed pp.1171–1173.
-/

public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.Mathieu
open Subgroup Theory.GroupTheory Sporadic.Mathieu.M24InvolutionCentralizers

/-- The exact source extension follows once the specified kernel's dihedral
factors are constructed; its normality and actual PSL3(2) quotient are proved. -/
theorem m24_twoA_dihedralExtension_of_kernel
    (h : IsDihedralCubeProduct TwoA.kernel) : IsM24DihedralExtension centralizer2A :=
  ⟨TwoA.kernel, inferInstance, h, ⟨TwoA.quotientEquiv⟩⟩

/-- The component exclusion for the literal marked 2A centralizer is unconditional. -/
theorem m24_twoA_no_component (K : Subgroup centralizer2A) :
    ¬ IsComponent centralizer2A K :=
  m24_no_component_of_kernel TwoA.exists_normal_selfCentralizing_twoKernel K

/-- Only the second representative's kernel remains in the table's component argument. -/
theorem m24_no_component_of_twoB_kernel
    (hB : ∃ Q : Subgroup centralizer2B,
      Q.Normal ∧ IsPGroup 2 Q ∧ centralizer (Q : Set centralizer2B) ≤ Q)
    (r : MulAut Sporadic.Mathieu.M24) (hr : orderOf r = 2) (K : Subgroup r.fixedSubgroup) :
    ¬ IsComponent r.fixedSubgroup K :=
  m24_no_component_of_representative_kernels
    TwoA.exists_normal_selfCentralizing_twoKernel hB r hr K

end CFSG.Quasithin.Chapter16.OtherPreliminaries.Mathieu
