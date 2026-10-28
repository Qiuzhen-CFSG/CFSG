module
public import CFSG.Quasithin.Chapter13.Section09.SourceCentralizer
public import Theory.SpecificGroups.SymmetricFourSmallQuotient
public import Theory.GroupTheory.NormalizedSupCard
public import CFSG.Quasithin.Chapter13.Section09.NormalizerStructure.CoreSpan

/-!
# S4 cores in z-conjugate centralizers

The four-core of an actual S4 maps trivially into the order-12 quotient
C_G(z)/Q, hence lies in the conjugate extraspecial core.
-/
public section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath
variable {G:Type*} [Group G] [Finite G] {d:Configuration G} (m:Marking d)

/-- The four-core of any actual S4 in a z-conjugate centralizer lies in the
corresponding original quaternion core. -/
theorem symmetricFour_core_le_conjugate_core
    {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G)
    (g:G) (X:Subgroup G) (eX:X≃*S4)
    (hX:X≤centralizer ({g*m.z*g⁻¹}:Set G)) :
    X.pCoreIn 2≤m.core.map (MulAut.conj g).toMonoidHom := by
  let C:=centralizer ({m.z}:Set G)
  let N:=m.core.subgroupOf C
  let : N.Normal:=m.marked_core_normal (hG.evenCharacteristic d.T)
  have hcard:Nat.card (C⧸N)=12 := by
    obtain ⟨e⟩:=m.centralizer_quotient_s3_c2 (hG.evenCharacteristic d.T) (m.centralizer_growth hG).1
    rw [Nat.card_congr e.toEquiv,Nat.card_prod]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,BinaryFourPlus.C2]
  let α:=MulAut.conj g
  let f:X→*C := (α.symm.toMonoidHom.comp X.subtype).codRestrict C (by
    intro x
    apply mem_centralizer_singleton_iff.mpr
    change α.symm (x:G)*m.z=m.z*α.symm (x:G)
    have hx:Commute (x:G) (α m.z):=mem_centralizer_singleton_iff.mp (hX x.property)
    simpa only [α.symm_apply_apply] using (hx.map α.symm).eq)
  let φ: X→*(C⧸N):=(QuotientGroup.mk' N).comp f
  have hk:pCore 2 X≤φ.ker :=
    Theory.SpecificGroups.SymmetricFour.twoCore_le_ker_of_equiv_of_card_lt eX φ (by rw [hcard];decide)
  rintro y ⟨x,hx,rfl⟩
  have he:QuotientGroup.mk' N (f x)=1:=hk hx
  have hxN:f x∈N := (QuotientGroup.eq_one_iff _).mp he
  refine ⟨α.symm (x:G),hxN,?_⟩
  exact α.apply_symm_apply (x:G)

/-- The intersection order follows from the original product and factor orders. -/
theorem card_B_inf_core (hE:IsEvenCharacteristicAt d.T) : Nat.card (m.B⊓m.core:Subgroup G)=8 := by
  let C:=centralizer ({m.z}:Set G)
  let : (m.core.subgroupOf C).Normal:=m.marked_core_normal hE
  have hQC:m.core≤C:=m.core_le_sylow.trans m.z_central_sylow
  have hCN:C≤normalizer (m.core:Set G):=(normal_subgroupOf_iff_le_normalizer hQC).mp inferInstance
  have hBC:m.B≤C:=(m.elementaryGroup_le_sylow false false).trans m.z_central_sylow
  have hc:=card_mul_eq_card_inf_mul_card_sup_of_normalizes m.core m.B (hBC.trans hCN)
  have hBQ:Nat.card (m.B⊔m.core:Subgroup G)=64:=m.three_core_overgroups.2.2.2.2.1
  rw [m.card_core,m.card_elementaryGroup false false,inf_comm,sup_comm,hBQ] at hc
  omega

/-- The actual ambient t-class in a conjugate Q stays in the conjugate B∩Q. -/
theorem conjugate_core_t_mem_intersection
    {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G) (g x:G)
    (hx:x∈m.core.map (MulAut.conj g).toMonoidHom) (ht:IsConj m.t x) :
    x∈(m.B⊓m.core).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨y,hy,rfl⟩:=hx
  have hty:IsConj m.t y:=ht.trans (isConj_iff.mpr ⟨g,rfl⟩).symm
  apply mem_map_of_mem
  rw [←m.core_t_class_closure hG]
  exact subset_closure ⟨hy,hty⟩

/-- In the actual source splitting, the whole second four-core lies in the
conjugate intersection whose centralizer is controlled by weak closure. -/
theorem symmetricFour_core_le_conjugate_intersection
    {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G)
    (g:G) (X:Subgroup G) (eX:X≃*S4)
    (hX:X≤centralizer ({g*m.z*g⁻¹}:Set G))
    (hfusion:∀x∈X.pCoreIn 2,x≠1→IsConj m.t x) :
    X.pCoreIn 2≤(m.B⊓m.core).map (MulAut.conj g).toMonoidHom := by
  intro x hx
  by_cases h1:x=1
  · exact h1 ▸ Subgroup.one_mem _
  · exact m.conjugate_core_t_mem_intersection hG g x
      (m.symmetricFour_core_le_conjugate_core hG g X eX hX hx) (hfusion x hx h1)

end CFSG.Quasithin.Chapter13.Section09.Marking
