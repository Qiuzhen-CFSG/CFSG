module
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.SourceCompletion.Nonsplit.TwoClasses
import all CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.SourceCompletion.Nonsplit.TwoClasses
public import Theory.SpecificGroups.AlternatingSix.M10.OuterInvolutions.Fixed

/-!
# The actual centralizer of a diagonal inverter

A fixed coset in C_G(B)/B lifts to an element commuting with the inverter:
its cubic commutator is removed by multiplying by its square. Involutions
of C_G(B) with the same quotient image coincide because the kernel is central
of order three. Thus the D10 fixed-subgroup conjugacy lifts to actual conjugacy
inside the original C_G(B) centralizer of the inverter.

Source: Aschbacher–Smith J.2.7(8), printed pp.436–437 (PDF pp.447–448).
-/

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

lemma kernel_cube (b : c.NB) (hb : (b:G)∈c.B) : b^3=1 := by
  have h := pow_card_eq_one' (x := (⟨b,hb⟩:c.B))
  rw [SourceCompletion.B_card c] at h
  apply Subtype.ext
  exact congrArg (fun a : c.B => (a:G)) h

public theorem involution_normalizer_image_order (x : c.NB) (hx : orderOf x=2) :
    orderOf (c.normalizerQuotientMap x)=2 := by
  apply orderOf_eq_prime
  · rw [←map_pow,←hx,pow_orderOf_eq_one,map_one]
  · intro he
    have hk : x∈c.normalizerQuotientMap.ker := he
    rw [c.normalizerQuotientMap_ker] at hk
    have h3 := c.kernel_cube x hk
    have hd := orderOf_dvd_of_pow_eq_one h3
    rw [hx] at hd
    norm_num at hd

lemma involutions_eq_of_cubic_image (x y : c.NB)
    (hyGB : (y:G)∈c.GB) (hx : x^2=1) (hy : y^2=1)
    (he : c.normalizerQuotientMap x=c.normalizerQuotientMap y) : x=y := by
  let b := x*y⁻¹
  have hb : (b:G)∈c.B := by
    have hk : b∈c.normalizerQuotientMap.ker := by
      change c.normalizerQuotientMap (x*y⁻¹)=1
      rw [map_mul,map_inv,he,mul_inv_cancel]
    rw [c.normalizerQuotientMap_ker] at hk
    exact hk
  have hby : Commute b y := Subtype.ext (hyGB b hb)
  have hbx : b*y=x := by dsimp [b];group
  have hb2 : b^2=1 := by
    have hh := hx
    rw [←hbx,hby.mul_pow,hy,mul_one] at hh
    exact hh
  have hb1 : b=1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 2 3)
      (orderOf_dvd_of_pow_eq_one hb2) (orderOf_dvd_of_pow_eq_one (c.kernel_cube b hb)))
  simpa only [hb1,one_mul] using hbx.symm

public theorem cubic_fixed_lift (u : c.NB) (hu : c.InvertsB (u:G))
    (a : c.NormalizerQuotient) (ha : a∈c.centralizerImage)
    (hfix : Commute (c.normalizerQuotientMap u) a) :
    ∃g:c.NB,(g:G)∈c.GB ∧ Commute u g ∧ c.normalizerQuotientMap g=a := by
  obtain ⟨g,hg,rfl⟩ := ha
  let b := ⁅u,g⁆
  have hbq : c.normalizerQuotientMap b=1 := by
    simp only [b,commutatorElement_def,map_mul,map_inv]
    exact commutatorElement_eq_one_iff_commute.mpr hfix
  have hb : (b:G)∈c.B := by
    have hk : b∈c.normalizerQuotientMap.ker := hbq
    rw [c.normalizerQuotientMap_ker] at hk
    exact hk
  have hb3 := c.kernel_cube b hb
  have hbi : b⁻¹=b^2 := by
    apply inv_eq_of_mul_eq_one_left
    rw [←pow_succ,hb3]
  have hub : u*b*u⁻¹=b⁻¹ := Subtype.ext (hu b hb)
  have hug : u*g*u⁻¹=b*g := by dsimp [b,commutatorElement_def];group
  refine ⟨b^2*g,c.GB.mul_mem
    (c.GB.pow_mem ((c.B_le_GB_of_card (SourceCompletion.B_card c)) hb) 2) hg,?_,?_⟩
  · apply mul_inv_eq_iff_eq_mul.mp
    calc
      u*(b^2*g)*u⁻¹=(u*b*u⁻¹)^2*(u*g*u⁻¹) := by rw [conj_pow];group
      _=(b⁻¹)^2*(b*g) := by rw [hub,hug]
      _=b⁻¹*g := by group
      _=b^2*g := by rw [hbi]
  · rw [map_mul,map_pow,hbq,one_pow,one_mul]

public theorem diagonal_fixed_involutions_conjugate_source
    (e : c.NormalizerQuotient ≃* AlternatingSix.ShadowLocal.AutA6)
    (hM : c.centralizerImage.map e.toMonoidHom=AlternatingSix.M10.extension)
    (u : c.NB) (hu : c.InvertsB (u:G)) (hu2 : orderOf u=2)
    (hn : e (c.normalizerQuotientMap u)∉AlternatingSix.ShadowLocal.natural)
    (x y : c.NB) (hxGB : (x:G)∈c.GB) (hyGB : (y:G)∈c.GB)
    (hx2 : orderOf x=2) (hy2 : orderOf y=2)
    (hux : Commute u x) (huy : Commute u y) :
    ∃a:c.NB,(a:G)∈c.GB ∧ Commute u a ∧ a*x*a⁻¹=y := by
  let f := e.toMonoidHom.comp c.normalizerQuotientMap
  have hxM : f x∈AlternatingSix.M10.extension := by
    rw [←hM]
    exact mem_map_of_mem e.toMonoidHom
      (mem_map_of_mem c.normalizerQuotientMap (show x∈c.GB.subgroupOf c.NB from hxGB))
  have hyM : f y∈AlternatingSix.M10.extension := by
    rw [←hM]
    exact mem_map_of_mem e.toMonoidHom
      (mem_map_of_mem c.normalizerQuotientMap (show y∈c.GB.subgroupOf c.NB from hyGB))
  obtain ⟨b,hbi,hbfix,hbxy⟩ := AlternatingSix.M10.OuterInvolutions.diagonal_fixed_involutions_conjugate
    (f u) (c.inverter_marked_order e u hu hu2) hn (f x) (f y)
    ((e.orderOf_eq _).trans (c.involution_normalizer_image_order x hx2))
    ((e.orderOf_eq _).trans (c.involution_normalizer_image_order y hy2))
    hxM hyM (hux.map f) (huy.map f)
  have hbM := AlternatingSix.M10.Action.inner_le_extension hbi
  rw [←hM] at hbM
  obtain ⟨b,hb,rfl⟩ := hbM
  change Commute (e (c.normalizerQuotientMap u)) (e b) at hbfix
  have hbfix' : Commute (c.normalizerQuotientMap u) b := by
    apply e.injective
    simpa only [map_mul] using hbfix.eq
  obtain ⟨a,ha,hua,hqa⟩ := c.cubic_fixed_lift u hu b hb hbfix'
  refine ⟨a,ha,hua,?_⟩
  apply c.involutions_eq_of_cubic_image (a*x*a⁻¹) y hyGB
  · rw [conj_pow,←hx2,pow_orderOf_eq_one];group
  · exact hy2 ▸ pow_orderOf_eq_one y
  · apply e.injective
    simp only [map_mul,map_inv,hqa]
    exact hbxy

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
