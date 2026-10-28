module

public import Theory.GroupTheory.NormalizingInvolutionCard
public import Theory.GroupTheory.SemidihedralStandardModel
public import Stellmacher.MainDefs
/-! An order-eight element and an involution acting by its cube generate
a semidihedral subgroup of order sixteen. This is used for the literal
PSL₂(25)⁺ normalizer in Aschbacher–Smith J.5.4. -/

public section
open Subgroup
namespace Semidihedral

theorem sixteen_of_pair {G : Type*} [Group G] [Finite G]
    (a b : G) (ha : orderOf a=8) (hb : orderOf b=2)
    (hab : b*a*b⁻¹=a^3) :
    Nat.card (zpowers a ⊔ zpowers b : Subgroup G)=16 ∧
      Stellmacher.IsSemidihedralGroup (zpowers a ⊔ zpowers b : Subgroup G) := by
  have ha8 : a^8=1 := ha ▸ pow_orderOf_eq_one a
  have hb2 : b^2=1 := hb ▸ pow_orderOf_eq_one b
  have hout : b∉zpowers a := by
    rintro ⟨k,rfl⟩
    have hc : Commute (a^k) a := (Commute.refl a).zpow_left k
    have he : a^3=a := hab.symm.trans (by rw [hc.eq,mul_inv_cancel_right])
    have he2 : a^2=1 := mul_right_cancel (show a^2*a=1*a by simpa [pow_succ] using he)
    have hd := orderOf_dvd_iff_pow_eq_one.mpr he2
    rw [ha] at hd
    norm_num at hd
  have hn : b∈normalizer (zpowers a : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq,MonoidHom.map_zpowers]
    change zpowers (b*a*b⁻¹)=zpowers a
    rw [hab]
    apply le_antisymm
    · exact zpowers_le.mpr ((zpowers a).pow_mem (mem_zpowers a) 3)
    · apply zpowers_le.mpr
      have h := (zpowers (a^3)).pow_mem (mem_zpowers (a^3)) 3
      have he : (a^3)^3=a := by rw [← pow_mul,show 3*3=8+1 from rfl,pow_succ,ha8,one_mul]
      rwa [he] at h
  have hcard : Nat.card (zpowers a ⊔ zpowers b : Subgroup G)=16 := by
    rw [card_sup_zpowers_of_normalizing_involution _ _ hb2 hout hn,Nat.card_zpowers,ha]
  let Q := zpowers a ⊔ zpowers b
  let ar : Q := ⟨a,mem_sup_left (mem_zpowers _)⟩
  let br : Q := ⟨b,mem_sup_right (mem_zpowers _)⟩
  have hgen : closure ({ar,br} : Set Q)=⊤ := by
    apply map_injective Q.subtype_injective
    rw [MonoidHom.map_closure,← MonoidHom.range_eq_map,Q.range_subtype]
    rw [Set.image_insert_eq,Set.image_singleton]
    change closure ({a,b} : Set G)=Q
    rw [← Set.singleton_union,Subgroup.closure_union,← zpowers_eq_closure,← zpowers_eq_closure]
  exact ⟨hcard,4,le_rfl,hcard,ar,br,(orderOf_coe ar).symm.trans ha,
    (orderOf_coe br).symm.trans hb,Subtype.ext hab,hgen⟩

/-- Transport preserves the actual cardinal and marked generator presentation. -/
theorem of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : Stellmacher.IsSemidihedralGroup G) : Stellmacher.IsSemidihedralGroup H := by
  obtain ⟨n,hn,hc,a,b,ha,hb,hab,hgen⟩ := h
  refine ⟨n,hn,(Nat.card_congr e.toEquiv).symm.trans hc,e a,e b,?_,?_,?_,?_⟩
  · exact (orderOf_injective e.toMonoidHom e.injective a).trans ha
  · exact (orderOf_injective e.toMonoidHom e.injective b).trans hb
  · simpa only [map_mul,map_inv,map_pow] using congrArg e hab
  · rw [← Set.image_singleton,← Set.image_insert_eq]
    change closure (e.toMonoidHom '' ({a,b} : Set G))=⊤
    rw [← MonoidHom.map_closure,hgen,map_top_of_surjective e.toMonoidHom e.surjective]

end Semidihedral
