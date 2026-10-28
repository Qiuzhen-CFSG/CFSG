module
public import Theory.GroupTheory.NormalCoreTwoClosedTransport
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Two-subgroups in a core-centralizing normal subgroup

Let X and C be normal in G, with G/X a two-group and [C,X] contained
in O₂(X). The kernel of C → G/X is central modulo its intersection
with O₂(X). Hence C has a normal Sylow two-subgroup, and every
two-subgroup of C lies in O₂(G).

This retains possible odd central kernels. The original seven-letter
application in Aschbacher--Smith 15.2.23 uses C as the action kernel
on the whole moved subgroup and G = XQI.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A two-group in a normal core-centralizing subgroup lies in the ambient two-core. -/
theorem twoGroup_le_pCore_of_normal_core_commutator (X C A : Subgroup G) [X.Normal] [C.Normal]
    (hquot : IsPGroup 2 (G ⧸ X)) (hcomm : ⁅C,X⁆ ≤ X.pCoreIn 2)
    (hA : IsPGroup 2 A) (hAC : A ≤ C) : A ≤ pCore 2 G := by
  let f := ((QuotientGroup.mk' X).comp C.subtype).rangeRestrict
  let N := (X.pCoreIn 2).subgroupOf C
  let : (X.pCoreIn 2).Normal := inferInstanceAs (((pCore 2 X).map X.subtype).Normal)
  have hk : N ≤ f.ker := by
    intro x hx
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff (N := X) (x : G)).mpr (pCoreIn_le 2 X hx)
  have hc : ⁅f.ker,⊤⁆ ≤ N := by
    apply commutator_le.mpr
    intro x hx y _
    have hxX : (x : G) ∈ X := (QuotientGroup.eq_one_iff (N := X) (x : G)).mp
      (congrArg Subtype.val hx)
    change ⁅(x : G),(y : G)⁆ ∈ X.pCoreIn 2
    exact hcomm (commutator_comm X C ▸ commutator_mem_commutator hxX y.property)
  have hi := odd_pCore_index_of_central_kernel_mod_two f
    (MonoidHom.rangeRestrict_surjective _) (hquot.to_subgroup _)
    N ((isPGroup_pCoreIn 2 X).comap_subtype) hk hc
  obtain ⟨P,hP⟩ := normalSylowTwo_of_odd_pCore_index hi
  let : (P : Subgroup C).Normal := hP
  have hpc : (P : Subgroup C) ≤ pCore 2 C := le_sSup ⟨hP,P.isPGroup'⟩
  have hAP : A.subgroupOf C ≤ P := by
    obtain ⟨Q,hQ⟩ := hA.comap_subtype.exists_le_sylow
    have he : (P : Subgroup C) = Q :=
      (P.is_maximal' Q.isPGroup' (P.isPGroup'.le_sylow_of_normal Q)).symm
    exact he ▸ hQ
  have hh := map_mono (f := C.subtype) (hAP.trans hpc)
  rw [map_subgroupOf_eq_of_le hAC] at hh
  exact hh.trans (le_sSup ⟨inferInstance,pCore_isPGroup.map C.subtype⟩)

end Subgroup
