module
public import CFSG.Quasithin.Chapter13.Section09.NormalizerStructure.Order
public import Theory.SpecificGroups.SymmetricFourWreath.InvolutionClasses.CoreGenerators
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The swapping involution fuses with z from original source inputs

The first noncentral Q orbit has centralizer A: three native generators
recover t and z and reduce the centralizer to the dihedral base. If its
C_G(z)-orbit avoided the swapping class, it would be invariant and force
C_G(z) to normalize A. The full growth theorem excludes containment in
N_G(A)=M. Thus the original swap is conjugate to z.

Source: Aschbacher–Smith 13.9.9, printed p.972.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath SymmetricFourWreath.InvolutionClasses
variable {G:Type*} [Group G] [Finite G] {d:Configuration G} (m:Marking d)

omit [Finite G] in
theorem gammaZeroGenerator_image_mem (i:Fin 3) :
    m.sylowModelEmbedding (gammaZeroGenerator i)∈m.coreLocalClass 0 := by
  rw [m.coreLocalClass_eq_image]
  exact ⟨gammaZeroGenerator i,gammaZeroGenerator_mem i,rfl⟩

omit [Finite G] in
theorem coreLocalClass_zero_le_A : m.coreLocalClass 0⊆m.elementaryGroup true true := by
  rw [m.coreLocalClass_eq_image]
  rintro x ⟨a,ha,rfl⟩
  have h:=gamma_zero_coordinates a ha
  apply mem_map_of_mem m.embedding
  exact (mem_elementary true true (sylowEmbedding a)).mpr ⟨h.1,⟨a.left 1,h.2.1,rfl⟩,⟨a.left turn,h.2.2,rfl⟩⟩

theorem centralizer_coreLocalClass_zero (hE:IsEvenCharacteristicAt d.T) :
    centralizer (m.coreLocalClass 0)=m.elementaryGroup true true := by
  apply le_antisymm
  · intro g hg
    have hcomm (i:Fin 3):Commute g (m.sylowModelEmbedding (gammaZeroGenerator i)) :=
      (hg _ (m.gammaZeroGenerator_image_mem i)).symm
    have ht:m.sylowModelEmbedding (gammaZeroGenerator 0)*m.sylowModelEmbedding (gammaZeroGenerator 2)=m.t := by
      rw [←map_mul,gammaZeroGenerator_t]
      change m.embedding (sylowEmbedding (pair (DihedralGroup.r 2,1)))=m.t
      rw [sylowEmbedding_axis]
      rfl
    have hz:m.sylowModelEmbedding (gammaZeroGenerator 1)*m.sylowModelEmbedding (gammaZeroGenerator 2)=m.z := by
      rw [←map_mul,gammaZeroGenerator_z,m.sylowModelEmbedding_center]
    have hgJ:g∈m.dihedralBase := by
      rw [←m.elementary_thompson,←m.marked_common_centralizer hE]
      constructor
      · exact mem_centralizer_singleton_iff.mpr (hz ▸ ((hcomm 1).mul_right (hcomm 2)).eq)
      · exact mem_centralizer_singleton_iff.mpr (ht ▸ ((hcomm 0).mul_right (hcomm 2)).eq)
    have hgT:=m.dihedralBase_le_sylow hgJ
    rw [←m.range_sylowModelEmbedding] at hgT
    obtain ⟨a,rfl⟩:=hgT
    have haJ:sylowEmbedding a∈SymmetricFourWreath.J:=
      (mem_map_iff_mem m.embedding_injective).mp hgJ
    have har:a.right=1:=((mem_J _).mp haJ).1
    have hfix:∀i:Fin 3,a*gammaZeroGenerator i=gammaZeroGenerator i*a := by
      intro i
      apply m.sylowModelEmbedding_injective
      simpa only [map_mul] using (hcomm i).eq
    have hc:=(gamma_zero_centralizer_certificate a har).mp hfix
    apply mem_map_of_mem m.embedding
    exact (mem_elementary true true (sylowEmbedding a)).mpr
      ⟨har,⟨a.left 1,hc.1,rfl⟩,⟨a.left turn,hc.2,rfl⟩⟩
  · intro g hg x hx
    exact congrArg Subtype.val
      ((IsElementaryAbelian.toIsMulCommutative (p:=2) (G:=m.elementaryGroup true true)).is_comm.comm
        (⟨x,m.coreLocalClass_zero_le_A hx⟩:m.elementaryGroup true true) ⟨g,hg⟩)


theorem swap_fused_z {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G) : IsConj m.z m.s := by
  classical
  by_contra hn
  let C:=centralizer ({m.z}:Set G)
  have hE:=hG.evenCharacteristic d.T
  let : (m.core.subgroupOf C).Normal:=m.marked_core_normal hE
  have hCN:C≤normalizer (m.core:Set G):=
    (normal_subgroupOf_iff_le_normalizer (m.core_le_sylow.trans m.z_central_sylow)).mp inferInstance
  let a:=m.sylowModelEmbedding (gammaZeroGenerator 0)
  have ha:a∈m.coreLocalClass 0:=m.gammaZeroGenerator_image_mem 0
  have hza:IsConj m.z a:=m.isConj_of_mem_localInvolutionClass 0 a ha.2.2
  have ha2:orderOf a=2 := by
    obtain ⟨g,hg⟩:=isConj_iff.mp hza
    rw [←hg]
    exact ((MulAut.conj g).orderOf_eq m.z).trans m.z_order
  have hsub:C.elementOrbit a⊆m.coreLocalClass 0 := by
    intro x hx
    have hxQ:x∈m.core:=elementOrbit_subset hCN ha.1 hx
    have hax:IsConj a x:=by obtain ⟨g,_,hg⟩:=hx;exact isConj_iff.mpr ⟨g,hg⟩
    have hzx:IsConj m.z x:=hza.trans hax
    have hxz:x≠m.z := by
      intro he
      obtain ⟨g,hg,hgx⟩:=hx
      have hgz:g*m.z*g⁻¹=m.z:=mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hg)
      apply ha.2.1
      exact (MulAut.conj g).injective (show (MulAut.conj g) a=(MulAut.conj g) m.z from hgx.trans (he.trans hgz.symm))
    have hx2:orderOf x=2:=(elementOrbit_orderOf hx).trans ha2
    obtain ⟨i,hi,_⟩:=m.local_involution_classes x (d.sylow_le (m.core_le_sylow hxQ)) hx2
    have hxi:x∈m.coreLocalClass i:=⟨hxQ,hxz,hi⟩
    have hconj:IsConj (m.embedding (representative i)) x:=m.isConj_of_mem_localInvolutionClass i x hi
    rcases m.coreLocalClass_indices i x hxi with rfl|rfl|rfl|rfl
    · exact hxi
    · exact False.elim (m.not_isConj_t_z (hconj.trans hzx.symm))
    · exact False.elim (m.not_isConj_t_z ((m.double_transposition_fused_t hE (m.centralizer_growth hG).1).trans
        (hconj.trans hzx.symm)))
    · exact False.elim (hn (hzx.trans hconj.symm))
  have horbit:C.elementOrbit a=m.coreLocalClass 0:=le_antisymm hsub
    ((m.coreLocalClass_sylow_orbit 0 a ha).trans (elementOrbit_mono m.z_central_sylow a))
  have hnC:C≤normalizer (m.coreLocalClass 0) := by
    intro g hg
    apply mem_set_normalizer_iff.mpr
    intro x
    rw [←horbit]
    constructor
    · rintro ⟨k,hk,rfl⟩
      exact ⟨g*k,C.mul_mem hg hk,by simp [mul_assoc]⟩
    · rintro ⟨k,hk,he⟩
      refine ⟨g⁻¹*k,C.mul_mem (C.inv_mem hg) hk,?_⟩
      have hh:=congrArg (fun y:G=>g⁻¹*y*g) he
      simpa only [mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using hh
  have hnorm:C≤normalizer (centralizer (m.coreLocalClass 0):Set G) := by
    have hh:=hnC.trans (normalizer_le_normalizer_closure (m.coreLocalClass 0))
    have hhh:=hh.trans (normalizer_le_normalizer_centralizer (Subgroup.closure (m.coreLocalClass 0)))
    simpa only [centralizer_closure] using hhh
  rw [m.centralizer_coreLocalClass_zero hE,m.normalizer_A] at hnorm
  exact (m.centralizer_growth hG).2 hnorm

end CFSG.Quasithin.Chapter13.Section09.Marking
