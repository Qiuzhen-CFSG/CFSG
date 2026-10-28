module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuFirstActor

/-!
# The actual middle subgroup contains the order-four quotient actor

The source core and squaring lift generate a subgroup of order 4096 in F₁.
Sylow conjugacy inside that same F₁ carries it to the unchanged T_F. The
lift's square is outside Q and its fourth power lies in Z, so its image
in the original quotient H/Q has order four; conjugation preserves this.
The resulting actor supplies the natural fixed-line calculation on U/Z.

Source: Aschbacher–Smith J.4.5, printed pp.441–442.
-/

public section
noncomputable section
open Subgroup MulAction
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} {p:Plane d}

/-- Conjugate any literal subgroup of the required order to the unchanged
source middle, using an element of the actual first endpoint. -/
theorem SourceChoice.conjugate_to_T_F (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) (S:Subgroup G)
    (hSF:S≤p.F₁ B5) (hS:Nat.card S=4096) :
    ∃h:p.F₁ B5,S.map (MulAut.conj (h:G)).toMonoidHom=p.T_F B5 := by
  let F:=p.F₁ B5
  let P:Sylow 2 F:=Sylow.ofCard (S.subgroupOf F) (by
    rw [Nat.card_congr (subgroupOfEquivOfLe hSF).toEquiv,hS,s.card_F₁ p B5 hi]
    decide +kernel)
  obtain ⟨T,hT⟩:=s.T_F_sylow_F₁ p B5 hi
  obtain ⟨h,hh⟩:=exists_smul_eq F P T
  have hm:(S.subgroupOf F).map (MulAut.conj h).toMonoidHom=(p.T_F B5).subgroupOf F:=by
    have he:=congrArg Sylow.toSubgroup hh
    rw [Sylow.smul_def,Sylow.pointwise_smul_def,Subgroup.pointwise_smul_def,hT] at he
    exact he
  have he:=congrArg (Subgroup.map F.subtype) hm
  have hecomp:F.subtype.comp (MulAut.conj h).toMonoidHom=
      (MulAut.conj (h:G)).toMonoidHom.comp F.subtype:=rfl
  rw [map_map,hecomp,←map_map,map_subgroupOf_eq_of_le hSF,
    map_subgroupOf_eq_of_le (p.T_F_le_F₁ B5)] at he
  exact ⟨h,he⟩

/-- The unchanged source middle contains an actor of order four on the actual
H/Q natural quotient. -/
theorem SourceChoice.exists_T_F_order_four_mod_Q (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    ∃g:p.T_F B5,orderOf (d.ru2.quotientMap
      (inclusion ((p.T_F_le_F₁ B5).trans (p.F₁_le_H B5)) g))=4 := by
  obtain ⟨e,c,g,hz,_ht,_hc,_hco,_ha,hgF,_hgB,_hgSq,hsq,_hfour,_hgfour,hnot,hcard⟩:=
    s.exists_firstCore_extension_actor B5 hi
  let S:=fiveHyperplane d B5⊔zpowers (g:G)
  have hSF:S≤p.F₁ B5:=sup_le (p.fiveHyperplane_le_F₁ B5) (zpowers_le.mpr hgF)
  obtain ⟨h,hh⟩:=s.conjugate_to_T_F B5 hi S hSF hcard
  let gH:d.toTypeRuSetup.H:=⟨g,p.F₁_le_H B5 hgF⟩
  have hq:orderOf (d.ru2.quotientMap gH)=4:=by
    apply @orderOf_eq_prime_pow _ _ (d.ru2.quotientMap gH) 1 2 ⟨Nat.prime_two⟩
    · intro he
      have hk:gH^2∈d.ru2.quotientMap.ker:=by
        change d.ru2.quotientMap (gH^2)=1
        rw [map_pow]
        simpa only [pow_one] using he
      rw [d.ru2.quotient_kernel] at hk
      have hgQ:(g:G)^2∈d.toTypeRuSetup.Q:=by
        change ((gH^2:d.toTypeRuSetup.H):G)∈d.toTypeRuSetup.Q at hk
        simpa only [coe_pow] using hk
      exact hnot ((s.F₁_inf_Q p B5 hi).le ⟨pow_mem hgF 2,hgQ⟩)
    · rw [←map_pow]
      change gH^4∈d.ru2.quotientMap.ker
      rw [d.ru2.quotient_kernel]
      change ((gH^4:d.toTypeRuSetup.H):G)∈d.toTypeRuSetup.Q
      rw [coe_pow]
      exact (d.ru2.natural.kernel_le.trans d.ru2.six.kernel_le)
        (firstCore_squaring_actor_four_mem_Z B5 e g hsq)
  have hgS:(g:G)∈S:=(show zpowers (g:G)≤S from le_sup_right) (mem_zpowers _)
  have hgT:((h:G)*(g:G)*(h:G)⁻¹)∈p.T_F B5:=by
    rw [←hh]
    exact mem_map_of_mem (MulAut.conj (h:G)).toMonoidHom hgS
  refine ⟨⟨(h:G)*(g:G)*(h:G)⁻¹,hgT⟩,?_⟩
  let hH:d.toTypeRuSetup.H:=⟨h,p.F₁_le_H B5 h.property⟩
  have he:(inclusion ((p.T_F_le_F₁ B5).trans (p.F₁_le_H B5))
      ⟨(h:G)*(g:G)*(h:G)⁻¹,hgT⟩)=hH*gH*hH⁻¹:=Subtype.ext rfl
  rw [he,map_mul,map_mul,map_inv]
  change orderOf (MulAut.conj (d.ru2.quotientMap hH) (d.ru2.quotientMap gH))=4
  rw [MulEquiv.orderOf_eq,hq]

end CFSG.Quasithin.ChapterJ.RuSubgroup
