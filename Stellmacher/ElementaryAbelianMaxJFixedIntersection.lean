module

public import Stellmacher.ElementaryAbelianMaxJFixedCenter
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# Elementary fixed subgroups of the Thompson subgroup

For an elementary two-subgroup U of a finite subgroup S, the intersection
Ω₁(Z(J(S))) ∩ U is exactly C_U(J(S)). The reverse containment applies the
maximal-elementary subgroup argument to the fixed subgroup itself; no
containment U ≤ J(S) is required. The central omega subgroup of S lies in
the central omega subgroup of J(S) by the same argument.

This is the fixed-center step used in Aschbacher–Smith, 14.1.7, printed
p.977, with the elementary Thompson convention of Stellmacher (2.2).
-/

public section

open Subgroup
namespace Stellmacher
variable {G : Type*} [Group G] [Finite G]

theorem omegaCenter_maxJ_inf_elementary_eq_fixed (S U : Subgroup G)
    [IsElementaryAbelian 2 U] (hUS : U ≤ S) :
    omegaOneCenterAmbient (elementaryAbelianMaxJ S) ⊓ U =
      U ⊓ centralizer (elementaryAbelianMaxJ S : Set G) := by
  let F := U ⊓ centralizer (elementaryAbelianMaxJ S : Set G)
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.of_le (show F ≤ U from inf_le_left)
  have hF : F ≤ omegaOneCenterAmbient (elementaryAbelianMaxJ S) :=
    elementary_centralizer_maxJ_le_omegaCenter S F (inf_le_left.trans hUS) inf_le_right
  apply le_antisymm
  · intro v hv
    exact ⟨hv.2, ((mem_omegaOneCenterAmbient_iff _ v).mp hv.1).2.2⟩
  · exact le_inf hF inf_le_left

theorem omegaCenter_le_omegaCenter_maxJ (S : Subgroup G) :
    omegaOneCenterAmbient S ≤ omegaOneCenterAmbient (elementaryAbelianMaxJ S) := by
  let := omegaOneCenterAmbient_elementaryAbelian S
  apply elementary_centralizer_maxJ_le_omegaCenter S (omegaOneCenterAmbient S)
  · intro z hz
    exact ((mem_omegaOneCenterAmbient_iff S z).mp hz).1
  · have hJS : elementaryAbelianMaxJ S ≤ S := sSup_le fun _ hA => hA.1
    intro z hz j hj
    exact ((mem_omegaOneCenterAmbient_iff S z).mp hz).2.2 j
      (hJS hj)

end Stellmacher
