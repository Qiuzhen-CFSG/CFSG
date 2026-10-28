module
public import Theory.SpecificGroups.SymmetricFourWreath.InvolutionClasses.TransferKernel
public import CFSG.Quasithin.Chapter13.Section09.LocalGeometry.InvolutionClasses
public import CFSG.Quasithin.Chapter13.Section09.FusionAlignment.Transfer

/-!
# The literal transfer reduction for source 13.9.9

Transport the native sign kernel into the original M. Its intersection
with the actual Sylow has index two, and its involutions lie in precisely
three local classes. Once the centralizer orbit fuses the double
transposition with t, Thompson transfer gives the two ambient classes.

Source: Aschbacher–Smith 13.9.9(5), printed p.972.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath SymmetricFourWreath.InvolutionClasses
variable {G:Type*} [Group G] {d:Configuration G} (m:Marking d)

def localTransferKernel : Subgroup G := m.image transferKernel

theorem localTransferKernel_index :
    (m.localTransferKernel.subgroupOf (d.T:Subgroup G)).index=2 := by
  rw [←m.image_standardSylow]
  change (transferKernel.map m.embedding).relIndex ((standardSylow:Subgroup W).map m.embedding)=2
  rw [relIndex_map_map_of_injective _ _ m.embedding_injective]
  exact transferKernel_sylow_index

theorem localTransferKernel_involution (x:G) (hx:x∈m.localTransferKernel) (ho:orderOf x=2) :
    x∈m.localInvolutionClass 0 ∨ x∈m.localInvolutionClass 1 ∨ x∈m.localInvolutionClass 3 := by
  obtain ⟨w,hw,rfl⟩:=hx
  have hw2 : orderOf w=2 := (orderOf_injective m.embedding m.embedding_injective w).symm.trans ho
  have hi:classIndex w=0 ∨ classIndex w=1 ∨ classIndex w=3 := (transferKernel_involution w hw2).mp hw
  have hc (i:Fin 6) (he:classIndex w=i) : m.embedding w∈m.localInvolutionClass i :=
    (m.embedding_mem_localInvolutionClass i w).mpr ((isConj_representative_iff i w).mpr ⟨hw2,he⟩)
  rcases hi with hi|hi|hi
  · exact Or.inl (hc 0 hi)
  · exact Or.inr (Or.inl (hc 1 hi))
  · exact Or.inr (Or.inr (hc 3 hi))

theorem isConj_of_mem_localInvolutionClass (i:Fin 6) (x:G) (hx:x∈m.localInvolutionClass i) :
    IsConj (m.embedding (representative i)) x := by
  obtain ⟨g,_,hg⟩:=hx
  exact isConj_iff.mpr ⟨g,hg⟩

variable [Finite G]
theorem two_involution_classes_of_double_transposition_fusion
    {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G)
    (h3:IsConj m.t (m.embedding (representative 3))) :
    ∀x:G,orderOf x=2→IsConj m.z x ∨ IsConj m.t x := by
  apply (FusionAlignment.two_classes_of_index_two_local_cover hG d m.localTransferKernel
    m.localTransferKernel_index m.z m.t m.z_order m.t_order
    (fun h=>m.not_isConj_t_z h.symm) ?_).2.2.2
  intro x hx ho
  rcases m.localTransferKernel_involution x hx ho with hc|hc|hc
  · exact Or.inl (m.isConj_of_mem_localInvolutionClass 0 x hc)
  · exact Or.inr (m.isConj_of_mem_localInvolutionClass 1 x hc)
  · exact Or.inr (h3.trans (m.isConj_of_mem_localInvolutionClass 3 x hc))

end CFSG.Quasithin.Chapter13.Section09.Marking
