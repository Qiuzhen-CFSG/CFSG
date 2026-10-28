module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.LocalInvolutionResidualSource
public import Theory.GroupTheory.DisjointConjugateCenter
/-!
# The actual ambient local residual and its central line

The literal component residual embeds in G with C_K(R)=⟨zK⟩ and is normalized
by C_K(zK). Its ambient center is exactly that same involution line, since
zK belongs to the residual. These are direct transports of the concrete
GL₂(3) centralizer calculation, retaining the original subgroup maps.
Source: Aschbacher--Smith 2.5.15, printed p.558.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05
open Subgroup Theory.GroupTheory ComponentSelection
variable {G : Type*} [Group G]

theorem local_residual_ambient_facts (K : Subgroup G)
    (hK : Nonempty (K ≃* Matrix.PSL3Three.PSL) ∨ Nonempty (K ≃* Sporadic.Mathieu.M11))
    (z : K) (hz : orderOf z = 2) :
    let R := (GLTwoThreeLocal.residual z).map K.subtype
    R ≤ K ∧ K ⊓ centralizer (R : Set G) = zpowers (z : G) ∧
      K ⊓ centralizer ({(z : G)} : Set G) ≤ normalizer (R : Set G) := by
  let R := GLTwoThreeLocal.residual z
  obtain ⟨_,hc,_⟩ := linear_three_or_mathieu_local_residual K hK z hz
  change centralizer (R : Set K) = zpowers z at hc
  have hmap : (centralizer (R : Set K)).map K.subtype =
      K ⊓ centralizer (R.map K.subtype : Set G) := by
    apply le_antisymm
    · exact le_inf (map_subtype_le _) (map_centralizer_le_centralizer_image _ _)
    · intro x hx
      refine ⟨⟨x,hx.1⟩,?_,rfl⟩
      intro r hr
      exact Subtype.ext (hx.2 r (mem_map_of_mem K.subtype hr))
  refine ⟨map_subtype_le _,?_,?_⟩
  · rw [←hmap,hc,MonoidHom.map_zpowers]
    rfl
  · intro x hx
    have hxC : (⟨x,hx.1⟩ : K) ∈ centralizer ({z} : Set K) := by
      apply mem_centralizer_singleton_iff.mpr
      exact Subtype.ext (mem_centralizer_singleton_iff.mp hx.2)
    have hxN := GLTwoThreeLocal.centralizer_le_normalizer_residual z hxC
    exact R.le_normalizer_map K.subtype (mem_map_of_mem K.subtype hxN)
theorem local_residual_ambient_center (K : Subgroup G)
    (hK : Nonempty (K ≃* Matrix.PSL3Three.PSL) ∨ Nonempty (K ≃* Sporadic.Mathieu.M11))
    (z : K) (hz : orderOf z = 2) :
    centerIn ((GLTwoThreeLocal.residual z).map K.subtype) = zpowers (z : G) := by
  obtain ⟨hRK,hRz,_⟩ := local_residual_ambient_facts K hK z hz
  have hzR : (z : G) ∈ (GLTwoThreeLocal.residual z).map K.subtype :=
    mem_map_of_mem K.subtype (GLTwoThreeLocal.centralElement_mem_residual z
      (localResidualCentralizerEquiv K hK z hz) hz)
  apply le_antisymm
  · exact (le_inf (inf_le_left.trans hRK) inf_le_right).trans_eq hRz
  · apply zpowers_le.mpr
    exact ⟨hzR,(hRz.symm ▸ mem_zpowers (z : G)).2⟩

end CFSG.Quasithin.Chapter2.Section05
