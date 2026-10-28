module
public import Theory.SpecificGroups.SymmetricFourWreath.InvolutionClasses.CoreOrbits
public import Theory.GroupAction.ElementConjugacyOrbit
public import CFSG.Quasithin.Chapter13.Section09.NormalizerStructure.Transfer
public import CFSG.Quasithin.Chapter13.Section09.CentralizerStructure.Source

/-!
# The six-point centralizer orbit and two ambient involution classes

The actual z-centralizer has order 384 and its t-centralizer is the
dihedral base of order 64. Its six-point t-orbit lies in Q; nonfusion
excludes the z-type orbit and cardinality excludes the eight-point swap
orbit. It therefore meets the double-transposition class. The native
sign-kernel transfer reduction now covers every ambient involution.

Source: Aschbacher–Smith 13.9.9(5), printed p.972.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath SymmetricFourWreath.InvolutionClasses
variable {G:Type*} [Group G] {d:Configuration G} (m:Marking d)

def coreLocalClass (i:Fin 6) : Set G := {x | x∈m.core ∧ x≠m.z ∧ x∈m.localInvolutionClass i}

theorem coreLocalClass_eq_image (i:Fin 6) :
    m.coreLocalClass i=m.sylowModelEmbedding '' gamma i := by
  ext x
  constructor
  · rintro ⟨⟨a,ha,rfl⟩,hz,hc⟩
    refine ⟨a,?_,rfl⟩
    apply (mem_gamma i a).mpr
    have hi:= (isConj_representative_iff i (sylowEmbedding a)).mp
      ((m.embedding_mem_localInvolutionClass i (sylowEmbedding a)).mp hc)
    refine ⟨ha,(orderOf_injective sylowEmbedding sylowEmbedding_injective a).symm.trans hi.1,?_,hi.2⟩
    intro he
    apply hz
    rw [he,m.sylowModelEmbedding_center]
  · rintro ⟨a,ha,rfl⟩
    obtain ⟨ha,ho,hz,hi⟩ := (mem_gamma i a).mp ha
    refine ⟨mem_map_of_mem m.sylowModelEmbedding ha,?_,?_⟩
    · intro he
      apply hz
      apply m.sylowModelEmbedding_injective
      rw [m.sylowModelEmbedding_center]
      exact he
    · exact (m.embedding_mem_localInvolutionClass i (sylowEmbedding a)).mpr
        ((isConj_representative_iff i (sylowEmbedding a)).mpr
          ⟨(orderOf_injective sylowEmbedding sylowEmbedding_injective a).trans ho,hi⟩)

theorem coreLocalClass_card (i:Fin 6) : (m.coreLocalClass i).ncard=gammaSize i := by
  rw [m.coreLocalClass_eq_image,Set.ncard_image_of_injective _ m.sylowModelEmbedding_injective]
  change Nat.card (gamma i)=_
  exact gamma_card i

theorem coreLocalClass_indices (i:Fin 6) (x:G) (hx:x∈m.coreLocalClass i) : i=0 ∨ i=1 ∨ i=3 ∨ i=5 := by
  rw [m.coreLocalClass_eq_image] at hx
  obtain ⟨a,ha,_⟩:=hx
  exact gamma_indices i a ha

theorem coreLocalClass_sylow_orbit (i:Fin 6) (x:G) (hx:x∈m.coreLocalClass i) :
    m.coreLocalClass i⊆(d.T:Subgroup G).elementOrbit x := by
  rw [m.coreLocalClass_eq_image] at hx ⊢
  obtain ⟨a,ha,rfl⟩:=hx
  rintro y ⟨b,hb,rfl⟩
  obtain ⟨ga,hga⟩:=gamma_representative_orbit i a ha
  obtain ⟨gb,hgb⟩:=gamma_representative_orbit i b hb
  let g:P:=gammaActor gb*(gammaActor ga)⁻¹
  have he:g*a*g⁻¹=b := by rw [←hga,←hgb];simp [g,mul_assoc]
  refine ⟨m.sylowModelEmbedding g,?_,?_⟩
  · rw [←m.range_sylowModelEmbedding]
    exact ⟨g,rfl⟩
  · simpa only [map_mul,map_inv] using congrArg m.sylowModelEmbedding he

variable [Finite G]

theorem centralizer_z_card (hE:IsEvenCharacteristicAt d.T)
    (hgrowth:(d.T:Subgroup G)<centralizer ({m.z}:Set G)) :
    Nat.card (centralizer ({m.z}:Set G))=384 := by
  let C:=centralizer ({m.z}:Set G)
  let N:=m.core.subgroupOf C
  let :N.Normal:=m.marked_core_normal hE
  obtain ⟨e⟩:=m.centralizer_quotient_s3_c2 hE hgrowth
  have hc:Nat.card (C⧸N)=12 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_prod]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial,BinaryFourPlus.C2]
  have hn:Nat.card N=32 := (Nat.card_congr
    (subgroupOfEquivOfLe (m.core_le_sylow.trans m.z_central_sylow)).toEquiv).trans m.card_core
  have h:=card_eq_card_quotient_mul_card_subgroup N
  rw [hc,hn] at h
  exact h

theorem centralizer_z_t_orbit_card (hE:IsEvenCharacteristicAt d.T)
    (hgrowth:(d.T:Subgroup G)<centralizer ({m.z}:Set G)) :
    ((centralizer ({m.z}:Set G)).elementOrbit m.t).ncard=6 := by
  have h:=elementOrbit_card (centralizer ({m.z}:Set G)) m.t (m.z_central_sylow m.t_mem_sylow)
  rw [m.marked_common_centralizer hE,m.elementary_thompson,Marking.dihedralBase,
    m.card_image,card_J,m.centralizer_z_card hE hgrowth] at h
  change ((centralizer ({m.z}:Set G)).elementOrbit m.t).ncard*64=384 at h
  omega


theorem centralizer_z_t_orbit_classes (hE:IsEvenCharacteristicAt d.T)
    (hgrowth:(d.T:Subgroup G)<centralizer ({m.z}:Set G)) (x:G)
    (hx:x∈(centralizer ({m.z}:Set G)).elementOrbit m.t) :
    x∈m.coreLocalClass 1 ∨ x∈m.coreLocalClass 3 := by
  let C:=centralizer ({m.z}:Set G)
  let :(m.core.subgroupOf C).Normal:=m.marked_core_normal hE
  have hCN:C≤normalizer (m.core:Set G) :=
    (normal_subgroupOf_iff_le_normalizer (m.core_le_sylow.trans m.z_central_sylow)).mp inferInstance
  have hxQ:x∈m.core:=elementOrbit_subset hCN m.t_mem_core hx
  have htx:IsConj m.t x:=by obtain ⟨g,_,hg⟩:=hx;exact isConj_iff.mpr ⟨g,hg⟩
  have hxz:x≠m.z:=by rintro rfl;exact m.not_isConj_t_z htx
  have hxo:orderOf x=2:=(elementOrbit_orderOf hx).trans m.t_order
  obtain ⟨i,hi,_⟩:=m.local_involution_classes x (d.sylow_le (m.core_le_sylow hxQ)) hxo
  have hxi:x∈m.coreLocalClass i:=⟨hxQ,hxz,hi⟩
  rcases m.coreLocalClass_indices i x hxi with rfl|rfl|rfl|rfl
  · exact False.elim (m.not_isConj_t_z (htx.trans (m.isConj_of_mem_localInvolutionClass 0 x hi).symm))
  · exact Or.inl hxi
  · exact Or.inr hxi
  · have hle:m.coreLocalClass 5⊆C.elementOrbit m.t := by
      calc
        _ ⊆ (d.T:Subgroup G).elementOrbit x := m.coreLocalClass_sylow_orbit 5 x hxi
        _ ⊆ C.elementOrbit x := elementOrbit_mono m.z_central_sylow x
        _ = C.elementOrbit m.t := elementOrbit_eq_of_mem hx
    have hc:=Set.ncard_le_ncard hle
    rw [m.coreLocalClass_card,m.centralizer_z_t_orbit_card hE hgrowth] at hc
    change 8≤6 at hc
    omega

theorem double_transposition_fused_t (hE:IsEvenCharacteristicAt d.T)
    (hgrowth:(d.T:Subgroup G)<centralizer ({m.z}:Set G)) :
    IsConj m.t (m.embedding (representative 3)) := by
  classical
  by_contra hn
  have hsub:(centralizer ({m.z}:Set G)).elementOrbit m.t⊆m.coreLocalClass 1 := by
    intro x hx
    rcases m.centralizer_z_t_orbit_classes hE hgrowth x hx with h1|h3
    · exact h1
    · have htx:IsConj m.t x:=by obtain ⟨g,_,hg⟩:=hx;exact isConj_iff.mpr ⟨g,hg⟩
      exact False.elim (hn (htx.trans (m.isConj_of_mem_localInvolutionClass 3 x h3.2.2).symm))
  have hc:=Set.ncard_le_ncard hsub
  rw [m.centralizer_z_t_orbit_card hE hgrowth,m.coreLocalClass_card] at hc
  change 6≤2 at hc
  omega

theorem two_involution_classes {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G)
    (hgrowth:(d.T:Subgroup G)<centralizer ({m.z}:Set G)) :
    ∀x:G,orderOf x=2→IsConj m.z x ∨ IsConj m.t x :=
  m.two_involution_classes_of_double_transposition_fusion hG
    (m.double_transposition_fused_t (hG.evenCharacteristic d.T) hgrowth)

end CFSG.Quasithin.Chapter13.Section09.Marking
