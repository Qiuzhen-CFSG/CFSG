module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadCoordinates
public import Theory.SpecificGroups.SymmetricSix.NaturalDihedralLifts

/-!
# Actual hexad dihedral lifts over the retained opposite radical

Two independent cosets of the original opposite radical have the same
kernel fixed four. The actual marked A₆ quotient supplies an involution
interchanging them. Correcting its lift inside the literal kernel then
forces a simultaneous fourth-power relation in the original hexad group.
The endpoint, opposite radical, kernel and quotient coordinates are retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}
local notation "Point" => Matrix.PSL3.LinearThree.pointParabolic Matrix.PSL3Four.F

/-- The original paired radicals supply the simultaneous dihedral lift
relation for every two independent opposite-radical cosets. -/
theorem TypeAt.hexad_dihedral_lifts (h : TypeAt z V)
    (W A B : Subgroup G) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hWV : W≤V) (hW4 : Nat.card W=4) (hWA : W≤A)
    (hAC : A≤centralizer (W:Set G)) (hAP : A⊓(normalizer (V:Set G)).pCoreIn 2=W)
    (c : G) (hc : c∈(normalizer (V:Set G)).pCoreIn 2) (hcW : c^2∉W)
    (hB : B=A.map (MulAut.conj c).toMonoidHom) (hi : A⊓B=W)
    (d : NaturalEndpointData A) (hBd : B≤d.carrier)
    (L : Subgroup G) (hPL : d.carrier≤L) (eL : L≃*Matrix.PSL3Four.PSL)
    (hmark : (d.carrier.subgroupOf L).map eL.toMonoidHom=Point)
    (x y : G) (hx : x∈B) (hy : y∈B) (hxW : x∉W) (hyW : y∉W) (hxyW : x*y∉W) :
    ∃ s : G, s∈d.hexad_overgroup ∧ orderOf s=2 ∧
      s*x*s⁻¹*y⁻¹∈A ∧ Commute x (s*x*s⁻¹) ∧ (x*s)^4=1 ∧ orderOf (x*s)=4 := by
  obtain ⟨_,_,hPD,_⟩ := d.hexad_overgroup_structure L hPL eL hmark
  obtain ⟨_,q,hq,hker,_,e,_,he⟩ := d.hexad_kernel_coordinates L hPL eL hmark
  have ker_mem {a : d.hexad_overgroup} (ha : a∈q.ker) : (a:G)∈A :=
    show a∈A.subgroupOf d.hexad_overgroup from hker ▸ ha
  let X : d.hexad_overgroup := ⟨x,hPD (hBd hx)⟩
  let Y : d.hexad_overgroup := ⟨y,hPD (hBd hy)⟩
  have hx2 : X^2=1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p:=2) x hx)
  have hy2 : Y^2=1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p:=2) y hy)
  have hxA : x∉A := fun hh => hxW (hi ▸ (show x∈A⊓B from ⟨hh,hx⟩))
  have hyA : y∉A := fun hh => hyW (hi ▸ (show y∈A⊓B from ⟨hh,hy⟩))
  have hqX : orderOf (q X)=2 := orderOf_eq_prime
    (by rw [←map_pow,hx2,map_one]) (fun he => hxA (ker_mem he))
  have hqY : orderOf (q Y)=2 := orderOf_eq_prime
    (by rw [←map_pow,hy2,map_one]) (fun he => hyA (ker_mem he))
  have hne : q X≠q Y := by
    intro hh
    have hprod : X*Y∈q.ker := by
      change q (X*Y)=1
      rw [map_mul,hh,←pow_two,←map_pow,hy2,map_one]
    apply hxyW
    rw [←hi]
    exact ⟨ker_mem hprod,B.mul_mem hx hy⟩
  have hfixX := h.paired_plane_radical_centralizer W A hWV hW4 hWA hAC hAP c hc hcW x (hB ▸ hx) hxW
  have hfixY := h.paired_plane_radical_centralizer W A hWV hW4 hWA hAC hAP c hc hcW y (hB ▸ hy) hyW
  have hfixed (a : d.hexad_overgroup) (ha : a∈q.ker) (hay : Commute a Y) : Commute a X := by
    have haA : (a:G)∈A := ker_mem ha
    have haw : (a:G)∈W := hfixY ▸
      (show (a:G)∈A⊓involutionCentralizer y from
        ⟨haA,mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hay.eq)⟩)
    have hac : (a:G)∈A⊓involutionCentralizer x := hfixX ▸ haw
    exact Subtype.ext (mem_centralizer_singleton_iff.mp hac.2)
  obtain ⟨s,hs2,_,hsq,hcomm,hfour,hqo⟩ :=
    Theory.SpecificGroups.SymmetricSix.NaturalExtensionLifts.exists_dihedral_lift_of_same_kernel_fixed
      q hq e (by intro g a; simpa only [Theory.SpecificGroups.SymmetricSix.polarRepresentation_apply] using he g a)
      X Y hx2 hy2 (Subtype.ext (setLike_mul_comm hx hy)) hqX hqY hne hfixed
  have hk : s*X*s⁻¹*Y⁻¹∈q.ker := by
    change q (s*X*s⁻¹*Y⁻¹)=1
    rw [map_mul,hsq,map_inv,mul_inv_cancel]
  have ho : orderOf (X*s)=4 := by
    have hd := orderOf_map_dvd q (X*s)
    have hd4 := orderOf_dvd_of_pow_eq_one hfour
    rw [hqo] at hd
    exact Nat.dvd_antisymm hd4 hd
  exact ⟨s,s.property,(orderOf_coe s).trans hs2,ker_mem hk,
    congrArg Subtype.val hcomm.eq,congrArg Subtype.val hfour,(orderOf_coe (X*s)).trans ho⟩

end CFSG.Quasithin.HigmanSims
