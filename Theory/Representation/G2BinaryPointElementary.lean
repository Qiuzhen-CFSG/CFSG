module
public import Theory.Representation.G2BinaryPointFlag
public import Theory.AtlasPort.LinearGroups.G2.BinaryNaturalPlane

/-!
# Normal elementary images in the binary point parabolic

An elementary subgroup of the original unipotent group, invariant under the
derived point parabolic, lies in the actual three-root subgroup ABC. Indeed
its elements commute with their conjugates by rootE and weylR. Five scalar
matrix equations, checked on the 64 unipotent parameter tuples, force the
last three root coordinates to vanish. The certificate only concerns these
five binary equations, not a subgroup-lattice enumeration.

Source: Aschbacher–Smith, Lemma 13.3.18, printed pp.894–895, the elementary
image of U_H in the natural point parabolic.
-/

public section
namespace Atlas.G2.Natural.BinaryPointFlag
open Atlas.G2.Restricted.NaturalCoordinates Atlas.G2.Explicit Subgroup

private def uact (t : Fin 6→F) (v : W) : W := ![
 v 0+t 5*v 1+t 3*(v 2+t 5*v 3)+t 2*v 5+
 t 1*(v 3+t 4*(v 4+t 5*v 5)+t 3*v 5)+t 0*(v 4+t 5*v 5),
 v 1+t 4*(v 2+t 5*v 3)+t 3*(v 4+t 5*v 5)+
 t 2*(v 3+t 4*(v 4+t 5*v 5)+t 3*v 5)+t 0*v 5,
 v 2+t 5*v 3+t 2*(v 4+t 5*v 5)+t 1*v 5,
 v 3+t 4*(v 4+t 5*v 5)+t 3*v 5,v 4+t 5*v 5,v 5]

private def ract (v : W) : W := ![v 0,v 2,v 1,v 4,v 3,v 5]
private def eact (v : W) : W := ![v 0,v 1+v 2,v 2,v 3+v 4,v 4,v 5]

private theorem action_unipotent (t : Fin 6→F) (v : W) :
    Restricted.NaturalCoordinates.action F (unipotentProduct t) v=uact t v := by
  simp only [unipotentProduct,map_mul,Module.End.mul_apply,
    action_rootA,action_rootB,action_rootC,action_rootD,action_rootE,action_rootF]
  have hs (x:F) : x^2=x := by revert x; decide +kernel
  ext i
  fin_cases i <;> simp [uact,hs]

private theorem involution_coordinate (t : Fin 6→F)
    (hs3 : uact t (uact t (Pi.single 3 1)) 0=0)
    (hs4 : uact t (uact t (Pi.single 4 1)) 0=0)
    (hr1 : uact t (ract (uact t (ract (Pi.single 1 1)))) 1=
      ract (uact t (ract (uact t (Pi.single 1 1)))) 1)
    (hr3 : uact t (ract (uact t (ract (Pi.single 3 1)))) 0=
      ract (uact t (ract (uact t (Pi.single 3 1)))) 0)
    (he4 : uact t (eact (uact t (eact (Pi.single 4 1)))) 0=
      eact (uact t (eact (uact t (Pi.single 4 1)))) 0) :
    t 3=0 ∧ t 4=0 ∧ t 5=0 := by
  revert t
  decide +kernel

/-- An elementary unipotent subgroup normalized by the derived point
parabolic lies in the actual three-root elementary subgroup ABC. -/
theorem elementary_normalized_point_le (A : Subgroup (Model F))
    [IsElementaryAbelian 2 A] (hA : A≤unipotent)
    (hn : BinaryParabolicPair.derivedSecondAmbient≤normalizer (A:Set (Model F))) :
    A≤BinaryCore.elementary := by
  intro x hx
  have hxu := hA hx
  rw [unipotent_eq_range] at hxu
  obtain ⟨t,rfl⟩ := hxu
  let x := unipotentProduct t
  have hs : x^2=1 := elemPow_eq_one_of_isElementaryAbelian (p:=2) x hx
  have hc (a:Model F) (ha:a∈BinaryParabolicPair.derivedSecondAmbient) :
      x*(a*x*a⁻¹)=(a*x*a⁻¹)*x := by
    have hay := (mem_normalizer_iff.mp (hn ha) x).mp hx
    exact congrArg Subtype.val ((inferInstance : IsMulCommutative A).is_comm.comm
      ⟨x,hx⟩ ⟨a*x*a⁻¹,hay⟩)
  have hE := hc (rootE 1) point_actor_membership.1
  have hR := hc weylR point_actor_membership.2.1
  have hwi : (weylR:Model F)⁻¹=weylR := inv_eq_of_mul_eq_one_left (by
    simpa [pow_two] using (weylR_sq (K:=F)))
  have hei : (rootE (1:F))⁻¹=rootE 1 := inv_eq_of_mul_eq_one_left (by
    rw [rootE_add,show (1:F)+1=0 by decide,rootE_zero])
  have hsq (i j : Fin 6) := congrArg
    (fun a:Model F => Restricted.NaturalCoordinates.action F a (Pi.single j 1) i) hs
  have hreq (i j : Fin 6) := congrArg
    (fun a:Model F => Restricted.NaturalCoordinates.action F a (Pi.single j 1) i) hR
  have heeq (i j : Fin 6) := congrArg
    (fun a:Model F => Restricted.NaturalCoordinates.action F a (Pi.single j 1) i) hE
  have hs3 : uact t (uact t (Pi.single 3 1)) 0=0 := by
    simpa only [x,pow_two,map_mul,Module.End.mul_apply,action_unipotent,map_one,
      Module.End.one_apply,Pi.single_eq_of_ne (by decide : (0:Fin 6)≠3)] using hsq 0 3
  have hs4 : uact t (uact t (Pi.single 4 1)) 0=0 := by
    simpa only [x,pow_two,map_mul,Module.End.mul_apply,action_unipotent,map_one,
      Module.End.one_apply,Pi.single_eq_of_ne (by decide : (0:Fin 6)≠4)] using hsq 0 4
  have hr1 := hreq 1 1
  have hr3 := hreq 0 3
  have he4 := heeq 0 4
  simp only [x,hwi,map_mul,Module.End.mul_apply,action_unipotent,action_weylR] at hr1 hr3
  simp only [x,hei,map_mul,Module.End.mul_apply,action_unipotent,action_rootE,one_mul] at he4
  obtain ⟨h3,h4,h5⟩ := involution_coordinate t hs3 hs4 hr1 hr3 he4
  refine ⟨⟨t 0,t 1,t 2,0,0⟩,⟨rfl,rfl⟩,?_⟩
  change unipotentProduct (BinaryCore.parameters ⟨t 0,t 1,t 2,0,0⟩)=unipotentProduct t
  congr 1
  ext i
  fin_cases i <;> simp [BinaryCore.parameters,h3,h4,h5]
end Atlas.G2.Natural.BinaryPointFlag
