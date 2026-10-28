module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.SixPath.Actor
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.SixPath.Cubic
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.ParabolicFamily.Inverted
public import Theory.SpecificGroups.SymmetricFive.EvenInvolutionCentralizer
public import Theory.GroupTheory.PrimeOrderLift

/-!
# Distinct involution images for the original six-path actor

The actual cubic in the second endpoint centralizes the short commutator
and carries its first long-root endpoint to the second. The genuine
four-distance actor puts the first endpoint at z and the commutator at zu.
After any displayed source frame carrying (zu,z) to (z,u), the cubic lies
in the original H and carries the original inverter to the actor. Its
order survives the two-group quotient kernel. An even involution of S5
has centralizer order eight, so the two images are distinct. This avoids
any unproved U-line identification and retains the actual quotient map.
Source: the final quotient separation in J.4.7, printed pp.444–445.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.PathTransport
open Subgroup Theory.GroupTheory
open Tits.ExceptionalParabolics.FullRee Tits.ExceptionalParabolics.FullRee.LongRootPaths
open ChapterF.SourceCompletion.BinaryRee
open Subgroup.CosetGeometry.RankTwo
open MarkedInverter MarkedSecondCore MarkedNormalizer Centralizers Centralizers.Choices ParabolicFamily
variable {D:Type*} [Group D] (q:Completion D)

private theorem completion_cubic_data : ∃w:D, orderOf w=3 ∧
    let z0:=completionLeftWord q*centralRoot q*(completionLeftWord q)⁻¹
    let z3:=q.left modelU
    let t:=z0*z3*z0⁻¹*z3⁻¹
    Commute w t ∧ w*z0*w⁻¹=z3 := by
  have hL : completionLeftWord q*centralRoot q*(completionLeftWord q)⁻¹=q.right modelLeft := by
    rw [centralRoot,modelZ_middle]
    change completionLeftWord q*q.middle (middleRoot 9)*(completionLeftWord q)⁻¹=_
    rw [completion_leftSix_conjugates]
    have hh:=DFunLike.congr_fun q.compatible (middleRoot 5)
    exact hh.trans (congrArg q.right (Subtype.ext leftSix_eq_rootfive.symm))
  have hR : q.left modelU=q.right modelRight := by
    rw [modelU_middle]
    have hh:=DFunLike.congr_fun q.compatible (middleRootOne^2)
    exact hh.trans (congrArg q.right (Subtype.ext middleRootOne_square_coe))
  have he:modelCubic*modelLeft*modelCubic⁻¹=modelRight := Subtype.ext cubicTransporter_conj_left
  have hc:Commute modelCubic modelShort := by
    show modelCubic*modelShort=modelShort*modelCubic
    exact Subtype.ext cubicTransporter_centralizes.eq
  have ht:modelLeft*modelRight*modelLeft⁻¹*modelRight⁻¹=modelShort := Subtype.ext commutator_eq_short
  refine ⟨q.right modelCubic,?_,?_⟩
  · exact (orderOf_injective q.right q.right_injective _).trans
      ((orderOf_injective second.subtype second.subtype_injective _).symm.trans cubicTransporter_order)
  · dsimp only
    rw [hL,hR,←map_inv,←map_inv,←map_mul,←map_mul,←map_mul,ht]
    exact ⟨hc.map q.right,by simpa only [map_mul,map_inv] using congrArg q.right he⟩

variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G}
  (p:Plane d) (c:Choices d) (B5:Sylow 5 d.H) (e:first≃*p.F₁ B5) (f:D→*G)
  (hf:Function.Injective f)
  (hleft:∀ b : first, f (q.left b)=(e b:G))
  (hz:(e modelZ:G)=c.z)
  (hfive:(zpowers modelRotation).map ((p.F₁ B5).subtype.comp e.toMonoidHom)=B5Image B5)

include c hz hfive in
private theorem inverter_even : d.ru2.quotientMap (sourceInverter p B5 e)∈alternatingGroup (Fin 5) := by
  obtain ⟨t,_,ht2,_,_,_⟩:=source_quotient_pentagons c B5 e hz hfive
  have he:t^2=sourceInverter p B5 e := Subtype.ext ht2
  rw [←he,map_pow]
  apply Equiv.Perm.mem_alternatingGroup.mpr
  simp only [map_pow]
  exact Int.units_sq _

include hf hleft hz hfive in
theorem source_quotient_actor (k:G)
    (hkcolor:k*(c.z*sourceU e)*k⁻¹=c.z) (hkz:k*c.z*k⁻¹=sourceU e) :
    ∃j:D, j•basePoint q=completionFourthWord q•basePoint q ∧
      f j*c.z*(f j)⁻¹=sourceU e ∧
      f j*(c.z*sourceU e)*(f j)⁻¹=c.z*sourceU e ∧
      ∃a:d.H, (a:G)=k*f j*k⁻¹ ∧
        orderOf (d.ru2.quotientMap a)=2 ∧
        d.ru2.quotientMap a≠d.ru2.quotientMap (sourceInverter p B5 e) := by
  obtain ⟨b,j,_,_,hjb,hjp,hjz,hjt,hbz⟩:=exists_six_actor q
  have hjzG:f j*c.z*(f j)⁻¹=sourceU e := by
    simpa only [map_mul,map_inv,centralRoot,hleft,hz,sourceU] using congrArg f hjz
  have hjtG:f j*(c.z*sourceU e)*(f j)⁻¹=c.z*sourceU e := by
    simpa only [map_mul,map_inv,centralRoot,hleft,hz,sourceU] using congrArg f hjt
  obtain ⟨w,hw,hwt,hwl⟩:=completion_cubic_data q
  let z0:=completionLeftWord q*centralRoot q*(completionLeftWord q)⁻¹
  let z3:=q.left modelU
  let t:=z0*z3*z0⁻¹*z3⁻¹
  let B:=f b
  let J:=f j
  have hx:B*f z0*B⁻¹=c.z := by
    simpa only [B,z0,map_mul,map_inv,centralRoot,hleft,hz] using congrArg f hbz
  have hy:B*f z3*B⁻¹=J := by
    simpa only [B,J,z3,map_mul,map_inv] using congrArg f hjb.symm
  have hz2:c.z*c.z=1 := by
    have hh:=pow_orderOf_eq_one c.z
    rw [SourceCompletion.z_order c,pow_two] at hh
    exact hh
  have hzi:c.z⁻¹=c.z := inv_eq_of_mul_eq_one_left hz2
  have ht:B*f t*B⁻¹=c.z*sourceU e := by
    have he:B*f t*B⁻¹=(B*f z0*B⁻¹)*(B*f z3*B⁻¹)*(B*f z0*B⁻¹)⁻¹*(B*f z3*B⁻¹)⁻¹ := by
      dsimp only [t]
      simp only [map_mul,map_inv]
      group
    rw [he,hx,hy,hzi]
    calc
      c.z*J*c.z*J⁻¹=c.z*(J*c.z*J⁻¹) := by group
      _=c.z*sourceU e := by rw [hjzG]
  let W:=k*(B*f w*B⁻¹)*k⁻¹
  have hW : Commute W c.z := by
    have hc:Commute (B*f w*B⁻¹) (c.z*sourceU e) := by
      have hh:Commute (B*f w*B⁻¹) (B*f t*B⁻¹) := (hwt.map f).map (MulAut.conj B).toMonoidHom
      rwa [ht] at hh
    have hh:=hc.map (MulAut.conj k).toMonoidHom
    change Commute W (k*(c.z*sourceU e)*k⁻¹) at hh
    rwa [hkcolor] at hh
  have hWH:W∈d.H := by
    rw [c.H_eq_centralizer_z]
    exact mem_centralizer_singleton_iff.mpr hW.eq
  let v:d.H:=⟨W,hWH⟩
  have hv:orderOf v=3 := by
    rw [←orderOf_coe]
    change orderOf (k*(B*f w*B⁻¹)*k⁻¹)=3
    exact ((MulAut.conj k).orderOf_eq _).trans
      (((MulAut.conj B).orderOf_eq _).trans ((orderOf_injective f hf w).trans hw))
  have hc:W*sourceU e*W⁻¹=k*J*k⁻¹ := by
    have hh:B*f w*B⁻¹*c.z*(B*f w*B⁻¹)⁻¹=J := by
      rw [←hx]
      calc
        _=B*f (w*z0*w⁻¹)*B⁻¹ := by simp only [map_mul,map_inv];group
        _=J := by rw [hwl];exact hy
    rw [←hkz]
    change (k*(B*f w*B⁻¹)*k⁻¹)*(k*c.z*k⁻¹)*(k*(B*f w*B⁻¹)*k⁻¹)⁻¹=_
    calc
      _=k*((B*f w*B⁻¹)*c.z*(B*f w*B⁻¹)⁻¹)*k⁻¹ := by group
      _=_ := by rw [hh]
  let a:d.H:=v*sourceInverter p B5 e*v⁻¹
  refine ⟨j,hjp,hjzG,hjtG,a,hc,?_,?_⟩
  · change orderOf (d.ru2.quotientMap (v*sourceInverter p B5 e*v⁻¹))=2
    rw [map_mul,map_mul,map_inv]
    exact ((MulAut.conj (d.ru2.quotientMap v)).orderOf_eq _).trans
      (source_quotient_order_two p B5 c e hz hfive)
  · have hk:IsPGroup 2 d.ru2.quotientMap.ker := by
      rw [d.ru2.quotient_kernel]
      exact (isPGroup_pCoreIn 2 d.H).comap_subtype
    have hvq:orderOf (d.ru2.quotientMap v)=3 :=
      (d.ru2.quotientMap.orderOf_map_eq_of_coprime_of_isPGroup_ker hk v (by rw [hv];decide)).trans hv
    change d.ru2.quotientMap (v*sourceInverter p B5 e*v⁻¹)≠_
    rw [map_mul,map_mul,map_inv]
    exact Equiv.Perm.three_conjugates_even_involution_five _ _
      (source_quotient_order_two p B5 c e hz hfive) (inverter_even p c B5 e hz hfive) hvq

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.PathTransport
