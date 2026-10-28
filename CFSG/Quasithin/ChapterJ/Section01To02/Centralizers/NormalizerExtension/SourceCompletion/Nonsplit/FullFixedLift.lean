module
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.SourceCompletion.Nonsplit.HFusion
import all CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.SourceCompletion.Nonsplit.FixedCentralizer

/-!
# The full fixed normalizer lifts through the inverted cubic kernel

For an inverter of the original B, every fixed quotient coset has a fixed
lift after cubic correction. A fixed kernel element has order dividing both
two and three, so is trivial. The literal quotient map therefore restricts
to an isomorphism on the full involution centralizer in N_G(B), retaining
its evaluation formula. This is the map used to lift the small Suzuki model.

Source: Aschbacher–Smith J.2.9, following J.2.7(3,7–10), printed p.438.
-/

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

public theorem normalizer_fixed_lift (u : c.NB) (hu : c.InvertsB (u:G))
    (a : c.NormalizerQuotient) (hfix : Commute (c.normalizerQuotientMap u) a) :
    ∃g:c.NB,Commute u g ∧ c.normalizerQuotientMap g=a := by
  obtain ⟨g,rfl⟩ := c.normalizerQuotientMap_surjective a
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
  refine ⟨b^2*g,?_,?_⟩
  · apply mul_inv_eq_iff_eq_mul.mp
    calc
      u*(b^2*g)*u⁻¹=(u*b*u⁻¹)^2*(u*g*u⁻¹) := by rw [conj_pow];group
      _=(b⁻¹)^2*(b*g) := by rw [hub,hug]
      _=b⁻¹*g := by group
      _=b^2*g := by rw [hbi]
  · rw [map_mul,map_pow,hbq,one_pow,one_mul]

public noncomputable def normalizerFixedMap (u : c.NB) :
    centralizer ({u}:Set c.NB) →* centralizer ({c.normalizerQuotientMap u}:Set c.NormalizerQuotient) where
  toFun x := ⟨c.normalizerQuotientMap x,
    mem_centralizer_singleton_iff.mpr (by
      exact congrArg c.normalizerQuotientMap (mem_centralizer_singleton_iff.mp x.property))⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)

public theorem normalizerFixedMap_bijective (u : c.NB) (hu : c.InvertsB (u:G)) :
    Function.Bijective (c.normalizerFixedMap u) := by
  constructor
  · apply (injective_iff_map_eq_one _).mpr
    intro x hx
    have hxq : c.normalizerQuotientMap (x:c.NB)=1 := congrArg Subtype.val hx
    have hxB : ((x:c.NB):G)∈c.B := by
      have hk : (x:c.NB)∈c.normalizerQuotientMap.ker := hxq
      rw [c.normalizerQuotientMap_ker] at hk
      exact hk
    have hx3 := c.kernel_cube (x:c.NB) hxB
    have hc : Commute u (x:c.NB) := (mem_centralizer_singleton_iff.mp x.property).symm
    have hi : u*(x:c.NB)*u⁻¹=(x:c.NB)⁻¹ := Subtype.ext (hu _ hxB)
    have hx2 : (x:c.NB)^2=1 := by
      have hh : (x:c.NB)=(x:c.NB)⁻¹ := hc.mul_inv_cancel.symm.trans hi
      calc
        (x:c.NB)^2=(x:c.NB)*(x:c.NB) := pow_two _
        _=(x:c.NB)⁻¹*(x:c.NB) := congrArg (fun a:c.NB => a*(x:c.NB)) hh
        _=1 := inv_mul_cancel _
    exact Subtype.ext (orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 2 3)
        (orderOf_dvd_of_pow_eq_one hx2) (orderOf_dvd_of_pow_eq_one hx3)))
  · intro y
    obtain ⟨x,hx,hxy⟩ := c.normalizer_fixed_lift u hu y
      (mem_centralizer_singleton_iff.mp y.property).symm
    exact ⟨⟨x,mem_centralizer_singleton_iff.mpr hx.symm.eq⟩,Subtype.ext hxy⟩

public noncomputable def normalizerFixedEquiv (u : c.NB) (hu : c.InvertsB (u:G)) :
    centralizer ({u}:Set c.NB) ≃* centralizer ({c.normalizerQuotientMap u}:Set c.NormalizerQuotient) :=
  MulEquiv.ofBijective (c.normalizerFixedMap u) (c.normalizerFixedMap_bijective u hu)

public theorem normalizerFixedEquiv_apply (u : c.NB) (hu : c.InvertsB (u:G))
    (x : centralizer ({u}:Set c.NB)) :
    (c.normalizerFixedEquiv u hu x : c.NormalizerQuotient)=c.normalizerQuotientMap x := by
  rfl

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
