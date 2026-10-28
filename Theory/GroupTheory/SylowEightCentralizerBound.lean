module
public import Theory.GroupTheory.NormalFourCentralizerSeparation
/-!
# A normal subgroup containing the Sylow center separates outside involution centralizers.
If eight divided such a centralizer, a Sylow eight there would be Sylow in
the whole group; the involution would lie in its center and hence in the
normal subgroup after Sylow conjugation. Source: Asc94 45.7(3), p.245.
-/
public section
open Subgroup
namespace Subgroup
variable {G:Type*} [Group G] [Finite G]
theorem not_eight_dvd_centralizer_of_sylow_center_le_normal (T:Sylow 2 G) (hT:Nat.card T=8) (C:Subgroup G) [C.Normal]
    (hZ:(center T).map (T:Subgroup G).subtype≤C)
    (x:G) (hx:orderOf x=2) (hxC:x∉C) : ¬8∣Nat.card (centralizer ({x}:Set G)) := by
  intro hd
  let D:=centralizer ({x}:Set G)
  let P:Sylow 2 D := default
  have hP8:8∣Nat.card P := P.pow_dvd_card_of_pow_dvd_card (n:=3) hd
  let Y:=(P:Subgroup D).map D.subtype
  have hYp:IsPGroup 2 Y := P.isPGroup'.map D.subtype
  obtain ⟨Q,hYQ⟩:=hYp.exists_le_sylow
  have hQcard:Nat.card Q=8 := by rw [Q.card_eq_multiplicity,←T.card_eq_multiplicity,hT]
  have hYcard:Nat.card Y=Nat.card P := card_map_of_injective D.subtype_injective
  have hYQeq:Y=(Q:Subgroup G) := eq_of_le_of_card_ge hYQ (by
    rw [hQcard,hYcard]
    exact Nat.le_of_dvd Nat.card_pos hP8)
  let x':D:=⟨x,mem_centralizer_singleton_iff.mpr rfl⟩
  have hxZ:x'∈center D := by
    apply mem_center_iff.mpr
    intro d
    apply Subtype.ext
    exact (mem_centralizer_singleton_iff.mp d.property)
  have hxc:orderOf x'=2 := (orderOf_injective D.subtype D.subtype_injective x').symm.trans hx
  have hn:(zpowers x').Normal := ⟨by
    intro y hy g
    have hc:=mem_center_iff.mp ((zpowers_le.mpr hxZ) hy) g
    simpa only [hc, mul_inv_cancel_right] using hy⟩
  let := hn
  have hxP:x'∈P := (IsPGroup.of_card (p:=2) (n:=1) (show Nat.card (zpowers x')=2 by rw [Nat.card_zpowers,hxc])).le_sylow_of_normal P (mem_zpowers x')
  have hxY:x∈Y := mem_map_of_mem D.subtype hxP
  have hQD:(Q:Subgroup G)≤D := hYQeq ▸ map_subtype_le _
  obtain ⟨g,hg⟩:=MulAction.exists_smul_eq G Q T
  let f:=MulAut.conj g
  have hmap:(Q:Subgroup G).map f.toMonoidHom=(T:Subgroup G) := by
    exact congrArg (fun A:Sylow 2 G=>(A:Subgroup G)) hg
  have hxT:f x∈T := by
    change f x∈(T:Subgroup G)
    rw [←hmap]
    exact mem_map_of_mem f.toMonoidHom (hYQeq ▸ hxY)
  have hxTc:(⟨f x,hxT⟩:T)∈center T := by
    apply mem_center_iff.mpr
    intro t
    obtain ⟨q,hq,he⟩:=mem_map.mp (hmap.symm ▸ (show (t:G)∈(T:Subgroup G) from t.property))
    apply Subtype.ext
    change (t:G)*f x=f x*(t:G)
    rw [←he]
    change f q*f x=f x*f q
    rw [←map_mul,←map_mul]
    exact congrArg f (mem_centralizer_singleton_iff.mp (hQD hq))
  have hxg:f x∈C := hZ (mem_map_of_mem (T:Subgroup G).subtype hxTc)
  have hh:=(inferInstance:C.Normal).conj_mem (f x) hxg g⁻¹
  apply hxC
  simpa [f,mul_assoc] using hh
end Subgroup
