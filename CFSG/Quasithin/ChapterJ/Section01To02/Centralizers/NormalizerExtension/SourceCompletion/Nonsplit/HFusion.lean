module
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.SourceCompletion.Nonsplit.FixedCentralizer
import all CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.SourceCompletion.Nonsplit.TwoClasses

/-!
# H controls the original s-class fusion

Conjugate two diagonal inverters in C_G(B), then correct that conjugator
inside the diagonal inverter's centralizer so that it fixes z. The corrected
conjugator lies in H=C_G(z). Earlier source transport turns every H-member
of the ambient s-class into such an inverter. This proves the actual equality
s^G intersect H = s^H and promotes the original T_s to Sylow in C_G(s).

Source: Aschbacher–Smith J.2.7(8,10), printed pp.436–437 (PDF pp.447–448).
-/

open Subgroup
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

lemma H_conjugate_diagonal_inverters_source
    (e : c.NormalizerQuotient ≃* AlternatingSix.ShadowLocal.AutA6)
    (hM : c.centralizerImage.map e.toMonoidHom=AlternatingSix.M10.extension)
    (u v : c.NB) (huH : (u:G)∈d.toTypeRuSetup.H) (hvH : (v:G)∈d.toTypeRuSetup.H)
    (hui : c.InvertsB (u:G)) (hvi : c.InvertsB (v:G))
    (hu2 : orderOf u=2) (hv2 : orderOf v=2)
    (hun : e (c.normalizerQuotientMap u)∉AlternatingSix.ShadowLocal.natural)
    (hvn : e (c.normalizerQuotientMap v)∉AlternatingSix.ShadowLocal.natural) :
    ∃h∈d.toTypeRuSetup.H,h*(u:G)*h⁻¹=(v:G) := by
  have hc := AlternatingSix.M10.OuterInvolutions.same_side_conjugate
    (e (c.normalizerQuotientMap u)) (e (c.normalizerQuotientMap v))
    (c.inverter_marked_order e u hui hu2) (c.inverter_marked_order e v hvi hv2)
    (c.inverter_marked_not_extension e hM u hui) (c.inverter_marked_not_extension e hM v hvi)
    (iff_of_false hun hvn)
  obtain ⟨g,hg,hgu⟩ := c.inverter_model_conjugacy_lift_source e hM u v hui hc
  let gN : c.NB := ⟨g,c.GB_le_NB hg⟩
  let zN : c.NB := ⟨c.z,c.GB_le_NB c.z_mem_GB⟩
  let xN := gN*zN*gN⁻¹
  have hguN : gN*u*gN⁻¹=v := Subtype.ext hgu
  have huz : Commute u zN := by
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (c.H_eq_centralizer_z ▸ huH)
  have hvz : Commute v zN := by
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (c.H_eq_centralizer_z ▸ hvH)
  have hvx : Commute v xN := by
    have hh := huz.map (MulAut.conj gN).toMonoidHom
    change Commute (gN*u*gN⁻¹) xN at hh
    rwa [hguN] at hh
  have hxGB : (xN:G)∈c.GB := c.GB.mul_mem
    (c.GB.mul_mem hg c.z_mem_GB) (c.GB.inv_mem hg)
  have hz2 : orderOf zN=2 := (Subgroup.orderOf_coe zN).symm.trans (SourceCompletion.z_order c)
  have hx2 : orderOf xN=2 := ((MulAut.conj gN).orderOf_eq zN).trans hz2
  obtain ⟨a,ha,hva,hax⟩ := c.diagonal_fixed_involutions_conjugate_source e hM
    v hvi hv2 hvn xN zN hxGB c.z_mem_GB hx2 hz2 hvx hvz
  refine ⟨(a:G)*g,?_,?_⟩
  · rw [c.H_eq_centralizer_z,mem_centralizer_singleton_iff]
    apply mul_inv_eq_iff_eq_mul.mp
    have hh := congrArg (fun b:c.NB => (b:G)) hax
    change (a:G)*(g*c.z*g⁻¹)*(a:G)⁻¹=c.z at hh
    calc
      ((a:G)*g)*c.z*((a:G)*g)⁻¹=(a:G)*(g*c.z*g⁻¹)*(a:G)⁻¹ := by group
      _=c.z := hh
  · calc
      ((a:G)*g)*(u:G)*((a:G)*g)⁻¹=(a:G)*(g*(u:G)*g⁻¹)*(a:G)⁻¹ := by group
      _=(a:G)*(v:G)*(a:G)⁻¹ := by rw [hgu]
      _=(v:G) := congrArg (fun b:c.NB => (b:G)) hva.symm.mul_inv_cancel

public theorem H_s_fusion_source : ∀x∈d.toTypeRuSetup.H,IsConj c.s x →
    ∃h∈d.toTypeRuSetup.H,h*c.s*h⁻¹=x := by
  obtain ⟨e,hM⟩ := c.normalizer_equiv_autA6_source
  obtain ⟨k,hk,hui,hu2⟩ := SourceCompletion.exists_inverter c
  let u : c.NB := ⟨k*c.s*k⁻¹,c.mem_NB_of_inverts hui⟩
  have hsu : IsConj c.s (u:G) := isConj_iff.mpr ⟨k,rfl⟩
  have huN : orderOf u=2 := (Subgroup.orderOf_coe u).symm.trans hu2
  have huH : (u:G)∈d.toTypeRuSetup.H := d.toTypeRuSetup.H.mul_mem
    (d.toTypeRuSetup.H.mul_mem hk (d.S_le_H c.s_mem.1)) (d.toTypeRuSetup.H.inv_mem hk)
  have hun : e (c.normalizerQuotientMap u)∉AlternatingSix.ShadowLocal.natural := by
    intro h
    exact c.not_isConj_z_s_source
      (hsu.trans (c.natural_inverter_z_fused_source e hM u hui huN h)).symm
  intro x hxH hsx
  have hx2 : orderOf x=2 := by
    obtain ⟨a,ha⟩ := isConj_iff.mp hsx
    rw [←ha]
    exact ((MulAut.conj a).orderOf_eq c.s).trans c.s_order_source
  have hxQ := (c.s_conjugate_mem_K_sdiff_Q (SourceCompletion.fusion c).2.2.1 hxH hsx).2
  obtain ⟨l,hl,hvi⟩ := c.H_inverter_transport_source x hxH hxQ hx2
  let v : c.NB := ⟨l*x*l⁻¹,c.mem_NB_of_inverts hvi⟩
  have hxv : IsConj x (v:G) := isConj_iff.mpr ⟨l,rfl⟩
  have hv2 : orderOf v=2 := (Subgroup.orderOf_coe v).symm.trans
    (((MulAut.conj l).orderOf_eq x).trans hx2)
  have hvH : (v:G)∈d.toTypeRuSetup.H := d.toTypeRuSetup.H.mul_mem
    (d.toTypeRuSetup.H.mul_mem hl hxH) (d.toTypeRuSetup.H.inv_mem hl)
  have hvn : e (c.normalizerQuotientMap v)∉AlternatingSix.ShadowLocal.natural := by
    intro h
    exact c.not_isConj_z_s_source
      (hsx.trans (hxv.trans (c.natural_inverter_z_fused_source e hM v hvi hv2 h))).symm
  obtain ⟨a,ha,he⟩ := c.H_conjugate_diagonal_inverters_source e hM u v
    huH hvH hui hvi huN hv2 hun hvn
  refine ⟨l⁻¹*a*k,d.toTypeRuSetup.H.mul_mem
    (d.toTypeRuSetup.H.mul_mem (d.toTypeRuSetup.H.inv_mem hl) ha) hk,?_⟩
  change a*(k*c.s*k⁻¹)*a⁻¹=l*x*l⁻¹ at he
  calc
    (l⁻¹*a*k)*c.s*(l⁻¹*a*k)⁻¹=l⁻¹*(a*(k*c.s*k⁻¹)*a⁻¹)*l := by group
    _=x := by rw [he];group


/-- The original T_s is a Sylow two-subgroup of the actual C_G(s). -/
public theorem Ts_sylow_source :
    ∃ P : Sylow 2 c.Gs, (P : Subgroup c.Gs) = c.Ts.subgroupOf c.Gs :=
  c.Ts_sylow_of_H_fusion (SourceCompletion.H_inf_Gs_eq_Ts c) c.H_s_fusion_source

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
