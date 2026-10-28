module
public import CFSG.Quasithin.Chapter13.Section09.LocalGeometry.InvolutionClasses.Reduction
public import CFSG.Quasithin.Chapter13.Section09.CentralizerGrowth

/-!
# The original weak-closure obstruction under C_G(z)=T

The marked swap has a local centralizer containing a three-cycle, so cannot
be conjugate to z when its centralizer is the two-group T. The native local
involution cover and Thompson transfer then force a distinct conjugate of z
inside the original B. This proves the first paragraph of 13.9.5 without
additional fusion assumptions.

Source: Aschbacher–Smith 13.9.5, printed p.970 (PDF p.987).
-/

public section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath
variable {G : Type*} [Group G] [Finite G] {d : Configuration G} (m : Marking d)

omit [Finite G] in
theorem not_isConj_z_s_of_centralizer_eq
    (hC : centralizer ({m.z}:Set G)=(d.T:Subgroup G)) : ¬IsConj m.z m.s := by
  exact CentralizerGrowth.not_isConj_z_swap d m.equiv
    (m.equiv.symm swap) (m.equiv.symm SymmetricFourWreath.z) turn
    (m.equiv.apply_symm_apply _) hC

theorem exists_conjugate_z_in_B_of_centralizer_eq
    {𝒦 : GroupClass} (hG : IsSimpleQTKE 𝒦 G)
    (hC : centralizer ({m.z}:Set G)=(d.T:Subgroup G)) :
    ∃x∈m.B,IsConj m.z x ∧ x≠m.z := by
  have hn := m.not_weakly_closed_z_of_centralizer_eq hG hC
    (m.not_isConj_z_s_of_centralizer_eq hC)
  push Not at hn
  exact hn
end CFSG.Quasithin.Chapter13.Section09.Marking
