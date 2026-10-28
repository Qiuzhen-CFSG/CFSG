module

public import CFSG.Quasithin.ChapterJ.Section04To05.SecondQuotient.Five
public import Theory.GroupAction.CentralElementaryQuotientOrbit

/-!
# The second core quotient is elementary of order sixteen

The actual symmetric-four core action is transitive on nonidentity R₂/S
cosets. An involution on the Q₅ line therefore supplies an involution in
every outside coset of the central elementary S/S₂. All elements of R₂/S₂
square to one. Since T=R₂Q₅, the original intersection line is central in
T/S₂. No elementary-extension or chosen cubic hypothesis is assumed.

Source: Aschbacher–Smith, J.4.4(1), printed p.441.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (p : Plane d)

private theorem rangeMap_eq_one (a : p.parabolic) :
    p.parabolicMap.rangeRestrict a=1 ↔ (a:G)∈d.toTypeRuSetup.S := by
  change a∈p.parabolicMap.rangeRestrict.ker ↔ _
  rw [MonoidHom.ker_rangeRestrict,p.parabolicMap_kernel]
  rfl

private theorem rangeMap_mem_core (a : p.parabolic) (ha : (a:G)∈p.R₂) :
    p.parabolicMap.rangeRestrict a∈pCore 2 p.parabolicMap.range := by
  have hcore : p.R₂.subgroupOf p.parabolic=pCore 2 p.parabolic := by
    rw [p.R₂_eq]
    exact comap_map_eq_self_of_injective p.parabolic.subtype_injective _
  have hk : IsPGroup 2 p.parabolicMap.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict,p.parabolicMap_kernel]
    exact (isPGroup_pCoreIn 2 d.L).comap_subtype
  change a∈(pCore 2 p.parabolicMap.range).comap p.parabolicMap.rangeRestrict
  rw [p.parabolicMap.rangeRestrict.comap_pCore_of_ker_isPGroup
    p.parabolicMap.rangeRestrict_surjective hk,← hcore]
  exact ha

/-- The full original parabolic supplies every nonzero quotient coset. -/
theorem Plane.secondBar_coset_orbit (z : p.SecondQuotient)
    (hz : z∈p.secondBar p.R₂) (hzn : z∉p.secondBar d.toTypeRuSetup.S)
    (x : p.SecondQuotient) (hx : x∈p.secondBar p.R₂)
    (hxn : x∉p.secondBar d.toTypeRuSetup.S) :
    ∃ g:p.SecondQuotient,x*(g*z*g⁻¹)⁻¹∈p.secondBar d.toTypeRuSetup.S := by
  obtain ⟨a,ha,rfl⟩ := hx
  obtain ⟨b,hb,rfl⟩ := hz
  have han : p.parabolicMap.rangeRestrict a≠1 := by
    intro h
    exact hxn ⟨a,(rangeMap_eq_one p a).mp h,rfl⟩
  have hbn : p.parabolicMap.rangeRestrict b≠1 := by
    intro h
    exact hzn ⟨b,(rangeMap_eq_one p b).mp h,rfl⟩
  obtain ⟨t,ht⟩ := Matrix.PSL3Two.ParabolicCoreModel.core_transitive
    p.parabolicImageEquivS4 _ _ (rangeMap_mem_core p b hb) (rangeMap_mem_core p a ha) hbn han
  obtain ⟨g,rfl⟩ := p.parabolicMap.rangeRestrict_surjective t
  have hs : ((a*(g*b*g⁻¹)⁻¹:p.parabolic):G)∈d.toTypeRuSetup.S := by
    apply (rangeMap_eq_one p _).mp
    rw [map_mul,map_inv,map_mul,map_mul,map_inv,ht,mul_inv_cancel]
  refine ⟨p.secondMap g,⟨a*(g*b*g⁻¹)⁻¹,hs,?_⟩⟩
  simp only [map_mul,map_inv]

/-- The genuine Q₅ source line discharges the elementary-extension step. -/
theorem SourceChoice.secondBar_R₂_elementary (s : SourceChoice p)
    (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hi : ∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    IsElementaryAbelian 2 (p.secondBar p.R₂) := by
  obtain ⟨z,hz,horder,hzn⟩ := s.exists_second_line p B5 hi
  have hm := hz ▸ mem_zpowers z
  let := p.secondBar_S_elementary
  apply elementary_of_central_involution_cosets
    (p.secondBar d.toTypeRuSetup.S) (p.secondBar p.R₂) p.secondBar_S_centralizes_R₂
    (fun n hn => elemPow_eq_one_of_isElementaryAbelian n hn) z
    (by rw [← horder]; exact pow_orderOf_eq_one z)
  exact fun x hx hxn => p.secondBar_coset_orbit z hm.2 hzn x hx hxn

/-- The actual second core quotient is elementary, without a selected five-subgroup premise. -/
theorem Plane.secondBar_R₂_elementary : IsElementaryAbelian 2 (p.secondBar p.R₂) := by
  obtain ⟨s⟩ := p.exists_sourceChoice
  obtain ⟨B5,hi⟩ := s.inverts_sylow_five
  exact s.secondBar_R₂_elementary p B5 hi

/-- The original intersection line is central in the literal Sylow image. -/
theorem Plane.secondBar_line_central (B5 : Sylow 5 d.toTypeRuSetup.H) :
    p.secondBar (Q₅ d B5)⊓p.secondBar p.R₂ ≤
      centralizer (p.secondBar (d.T : Subgroup G) : Set p.SecondQuotient) := by
  let := p.secondBar_R₂_elementary
  let := p.secondBar_Q₅_elementary B5
  apply le_centralizer_iff.mp
  rw [← p.R₂_sup_Q₅ B5,p.secondBar_sup _ _
    (p.R₂_le_T.trans p.sylow_le_parabolic)
    ((show Q₅ d B5≤(d.T:Subgroup G) from (p.R₂_sup_Q₅ B5) ▸ le_sup_right).trans
      p.sylow_le_parabolic)]
  apply sup_le
  · intro x hx y hy
    exact congrArg Subtype.val (mul_comm' (⟨y,hy.2⟩:p.secondBar p.R₂) ⟨x,hx⟩)
  · intro x hx y hy
    exact congrArg Subtype.val (mul_comm' (⟨y,hy.1⟩:p.secondBar (Q₅ d B5)) ⟨x,hx⟩)

/-- J.4.4(1) on the original Q₅ and original second quotient. -/
theorem SourceChoice.source_second_line (s : SourceChoice p)
    (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hi : ∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    IsElementaryAbelian 2 (p.secondBar (Q₅ d B5)) ∧
      Nat.card (p.secondBar (Q₅ d B5))=4 ∧
      IsElementaryAbelian 2 (p.secondBar p.R₂) ∧ Nat.card (p.secondBar p.R₂)=16 ∧
      ∃ a:p.SecondQuotient,orderOf a=2 ∧
        zpowers a=p.secondBar (Q₅ d B5)⊓p.secondBar p.R₂ ∧
        a∈centralizer (p.secondBar (d.T:Subgroup G):Set p.SecondQuotient) ∧
        a∉p.secondBar d.toTypeRuSetup.S := by
  obtain ⟨a,ha,ho,hn⟩ := s.exists_second_line p B5 hi
  exact ⟨p.secondBar_Q₅_elementary B5,s.secondBar_Q₅_card p B5 hi,
    p.secondBar_R₂_elementary,p.secondBar_R₂_card,
    a,ho,ha,p.secondBar_line_central B5 (ha ▸ mem_zpowers a),hn⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup
