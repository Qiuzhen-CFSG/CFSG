module
public import Theory.GroupTheory.ElementaryPairNorm
/-!
# The derived group of a fixed elementary pair

An involution exchanges two elementary factors of a group with elementary
central derived group. If every fixed central element is a central
coboundary, diagonal norms can be corrected into the fixed group. Their
commutators are precisely the central displacements of cross commutators.
Since cross commutators generate the derived group, the fixed center lies
in the derived subgroup of the full fixed group.

Source application: Aschbacher–Smith, Lemma 2.4.14 and its use in 2.4.21,
printed pp.533 and536. No classification of the fixed group is needed.
-/
public section
open Subgroup
open scoped Pointwise IsMulCommutative commutatorElement
namespace Subgroup
variable {G : Type*} [Group G]

theorem elementary_pair_fixed_center_le_derived
    (R U V Z : Subgroup G) [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 V]
    (hgen : U ⊔ V = R) (hRU : R ≤ normalizer (U : Set G))
    (hZ : U ⊓ V = Z) (hder : ⁅R,R⁆ = Z) (hcent : Z ≤ centralizer (R : Set G))
    (a : MulAut G) (ha : ∀ x, a (a x)=x) (hUV : U.map a.toMonoidHom=V)
    (htrace : ∀ z ∈ Z, a z=z → ∃ w ∈ Z, z=w*(a w)⁻¹) :
    Z ⊓ a.toMonoidHom.eqLocus (MonoidHom.id G) ≤
      ⁅R ⊓ a.toMonoidHom.eqLocus (MonoidHom.id G),R ⊓ a.toMonoidHom.eqLocus (MonoidHom.id G)⁆ := by
  let C := R ⊓ a.toMonoidHom.eqLocus (MonoidHom.id G)
  let D := ⁅C,C⁆
  have hUR : U ≤ R := le_sup_left.trans_eq hgen
  have hVR : V ≤ R := le_sup_right.trans_eq hgen
  have hZU : Z ≤ U := hZ ▸ inf_le_left
  have hZR : Z ≤ R := hZU.trans hUR
  have hau {u : G} (hu : u ∈ U) : a u ∈ V := hUV ▸ mem_map_of_mem a.toMonoidHom hu
  have hav {v : G} (hv : v ∈ V) : a v ∈ U := by
    obtain ⟨u,hu,he⟩ := (show v ∈ U.map a.toMonoidHom from hUV.symm ▸ hv)
    have he' : a u=v := he
    rw [←he',ha]
    exact hu
  have haZ {z : G} (hz : z ∈ Z) : a z ∈ Z := by
    have hz' : z ∈ U ⊓ V := hZ.symm ▸ hz
    exact hZ ▸ (show a z ∈ U ⊓ V from ⟨hav hz'.2,hau hz'.1⟩)
  have hzInv {z : G} (hz : z ∈ Z) : z⁻¹=z := inv_eq_of_mul_eq_one_left (by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p:=2) z (hZU hz))
  have hcross {x y : G} (hx : x ∈ R) (hy : y ∈ R) : ⁅x,y⁆ ∈ Z :=
    hder ▸ commutator_mem_commutator hx hy
  have hcomm {x y r : G} (hx : x ∈ R) (hy : y ∈ R) (hr : r ∈ R) :
      Commute r ⁅x,y⁆ := mem_centralizer_iff.mp (hcent (hcross hx hy)) r hr
  have hleft {x y z : G} (hx : x ∈ R) (hy : y ∈ R) (hz : z ∈ R) :
      ⁅x*y,z⁆=⁅x,z⁆*⁅y,z⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul, (hcomm hy hz hx).eq, mul_inv_cancel_right]
    exact (hcomm hy hz (commutator_le_self R (commutator_mem_commutator hx hz))).symm.eq
  have hright {x y z : G} (hx : x ∈ R) (hy : y ∈ R) (hz : z ∈ R) :
      ⁅x,y*z⁆=⁅x,y⁆*⁅x,z⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj]
    calc
      _ = ⁅x,y⁆*(y*⁅x,z⁆)*y⁻¹ := by group
      _ = ⁅x,y⁆*⁅x,z⁆ := by rw [(hcomm hx hz hy).eq];group
  have hcorrect (u : G) (hu : u ∈ U) : ∃ z ∈ Z, u*a u*z ∈ C := by
    let q := ⁅u,a u⁆
    have hq : q ∈ Z := hcross (hUR hu) (hVR (hau hu))
    have hqfix : a q=q := by
      change a ⁅u,a u⁆=⁅u,a u⁆
      rw [map_commutatorElement,ha,←commutatorElement_inv]
      exact hzInv hq
    obtain ⟨z,hz,hztrace⟩ := htrace q hq hqfix
    have hui : u⁻¹=u := inv_eq_of_mul_eq_one_left (by
      simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p:=2) u hu)
    have haui : (a u)⁻¹=a u := by rw [←map_inv,hui]
    have haz : a z=q*z := by
      have hh : q*a z=z := by rw [hztrace];group
      calc
        a z=q⁻¹*(q*a z) := by group
        _=q*z := by rw [hzInv hq,hh]
    refine ⟨z,hz,R.mul_mem (R.mul_mem (hUR hu) (hVR (hau hu))) (hZR hz),?_⟩
    change a (u*a u*z)=u*a u*z
    rw [map_mul,map_mul,ha,haz]
    change (a u*u)*(⁅u,a u⁆*z)=(u*a u)*z
    have haN : a u*u=(u*a u)⁻¹ := by simp only [mul_inv_rev,hui,haui]
    have hqN : ⁅u,a u⁆=(u*a u)*(u*a u) := by rw [commutatorElement_def,hui,haui];group
    rw [haN,hqN]
    group
  let δ : Z →* G := {
    toFun z := (z:G)*(a z)⁻¹
    map_one' := by simp
    map_mul' x y := by
      have hc : Commute (y:G) (a x) := mem_centralizer_iff.mp (hcent (haZ x.property)) y (hZR y.property)
      change ((x:G)*(y:G))*(a ((x:G)*(y:G)))⁻¹=((x:G)*(a x)⁻¹)*((y:G)*(a y)⁻¹)
      rw [map_mul,mul_inv_rev]
      have hc' : Commute (a y)⁻¹ (a x)⁻¹ :=
        (show Commute (a y) (a x) from
          mem_centralizer_iff.mp (hcent (haZ x.property)) (a y) (hZR (haZ y.property))).inv_left.inv_right
      calc
        _ = (x:G)*((y:G)*((a y)⁻¹*(a x)⁻¹)) := by group
        _ = (x:G)*((y:G)*((a x)⁻¹*(a y)⁻¹)) := by rw [hc'.eq]
        _ = ((x:G)*(a x)⁻¹)*((y:G)*(a y)⁻¹) := by rw [←mul_assoc (y:G),hc.inv_right.eq];group }
  have hnormcomm (u v : G) (hu : u ∈ U) (hv : v ∈ U) :
      ⁅u,a v⁆*(a ⁅u,a v⁆)⁻¹ ∈ D := by
    obtain ⟨z,hz,huz⟩ := hcorrect u hu
    obtain ⟨w,hw,hvw⟩ := hcorrect v hv
    have hzR := hZR hz
    have hwR := hZR hw
    have hunR := R.mul_mem (hUR hu) (hVR (hau hu))
    have hvnR := R.mul_mem (hUR hv) (hVR (hau hv))
    have hzcomm (r : G) (hr : r ∈ R) : ⁅z,r⁆=1 :=
      ((mem_centralizer_iff.mp (hcent hz)) r hr).symm |> Commute.commutator_eq
    have hwcomm (r : G) (hr : r ∈ R) : ⁅r,w⁆=1 :=
      ((mem_centralizer_iff.mp (hcent hw)) r hr) |> Commute.commutator_eq
    have hUU : ⁅u,v⁆=1 :=
      (show Commute u v from congrArg Subtype.val (mul_comm (⟨u,hu⟩:U) ⟨v,hv⟩)).commutator_eq
    have hVV : ⁅a u,a v⁆=1 :=
      (show Commute (a u) (a v) from congrArg Subtype.val
        (mul_comm (⟨a u,hau hu⟩:V) ⟨a v,hau hv⟩)).commutator_eq
    have he : ⁅u*a u*z,v*a v*w⁆=⁅u,a v⁆*(a ⁅u,a v⁆)⁻¹ := by
      rw [hleft hunR hzR (R.mul_mem hvnR hwR),hzcomm _ (R.mul_mem hvnR hwR),mul_one,
        hright hunR hvnR hwR,hwcomm _ hunR,mul_one,
        hleft (hUR hu) (hVR (hau hu)) hvnR,
        hright (hUR hu) (hUR hv) (hVR (hau hv)),
        hright (hVR (hau hu)) (hUR hv) (hVR (hau hv)),hUU,hVV,one_mul,mul_one,
        map_commutatorElement,ha,hzInv (hcross (hVR (hau hu)) (hUR hv))]
    exact he ▸ commutator_mem_commutator huz hvw
  let E := (D.comap δ).map Z.subtype
  have hcrossE (u v : G) (hu : u ∈ U) (hv : v ∈ V) : ⁅u,v⁆ ∈ E := by
    obtain ⟨w,hw,he⟩ := (show v ∈ U.map a.toMonoidHom from hUV.symm ▸ hv)
    have he' : a w=v := he
    refine ⟨⟨⁅u,v⁆,hcross (hUR hu) (hVR hv)⟩,?_,rfl⟩
    change ⁅u,v⁆*(a ⁅u,v⁆)⁻¹ ∈ D
    rw [←he']
    exact hnormcomm u w hu hw
  have hform (r : G) (hr : r ∈ R) : ∃ u ∈ U, ∃ v ∈ V, u*v=r := by
    change r ∈ (U:Set G)*(V:Set G)
    rw [←coe_mul_of_right_le_normalizer_left U V (hVR.trans hRU),hgen]
    exact hr
  have hZE : Z ≤ E := by
    rw [←hder]
    apply commutator_le.mpr
    intro r hr s hs
    obtain ⟨u,hu,v,hv,rfl⟩ := hform r hr
    obtain ⟨w,hw,x,hx,rfl⟩ := hform s hs
    have hUU : ⁅u,w⁆=1 :=
      (show Commute u w from congrArg Subtype.val (mul_comm (⟨u,hu⟩:U) ⟨w,hw⟩)).commutator_eq
    have hVV : ⁅v,x⁆=1 :=
      (show Commute v x from congrArg Subtype.val (mul_comm (⟨v,hv⟩:V) ⟨x,hx⟩)).commutator_eq
    rw [hleft (hUR hu) (hVR hv) (R.mul_mem (hUR hw) (hVR hx)),
      hright (hUR hu) (hUR hw) (hVR hx),hright (hVR hv) (hUR hw) (hVR hx),
      hUU,hVV,one_mul,mul_one,←commutatorElement_inv w v]
    exact E.mul_mem (hcrossE u x hu hx) (E.inv_mem (hcrossE w v hw hv))
  rintro z ⟨hz,hzf⟩
  obtain ⟨w,hw,he⟩ := htrace z hz hzf
  have hh : (⟨w,hw⟩ : Z) ∈ D.comap δ := (mem_map_iff_mem Z.subtype_injective).mp (hZE hw)
  change w*(a w)⁻¹ ∈ D at hh
  exact he.symm ▸ hh
end Subgroup
