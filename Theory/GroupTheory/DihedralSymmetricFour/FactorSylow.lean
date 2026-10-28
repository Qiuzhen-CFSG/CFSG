module
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.SpecificGroups.SymmetricFourSylow
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.DihedralInvolutionLift
/-!
# Sylow placement in a literal dihedral/symmetric product

The internal product coordinates make the factors normal. The first factor
lies in every Sylow two-subgroup; intersection with the second factor is
Sylow there. Its central dihedral involution centralizes the original whole
Sylow subgroup. These preserve the inclusions needed by 13.9.10.
-/

public section
open Subgroup
namespace DihedralSymmetricFour
variable {G:Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Each factor of a literal internal direct-product splitting is normal. -/
theorem split_factor_normal (C R X:Subgroup G) (hR:R≤C) (hX:X≤C)
    (split:C≃*R×X)
    (hc:∀c:C,(c:G)=((split c).1:G)*((split c).2:G))
    (hcomm:R≤centralizer (X:Set G)) :
    (R.subgroupOf C).Normal ∧ (X.subgroupOf C).Normal := by
  have hs:C=R⊔X := by
    apply le_antisymm
    · intro c hcC
      have he : c=((split ⟨c,hcC⟩).1:G)*((split ⟨c,hcC⟩).2:G) := hc ⟨c,hcC⟩
      rw [he]
      exact mul_mem_sup (split ⟨c,hcC⟩).1.property (split ⟨c,hcC⟩).2.property
    · exact sup_le hR hX
  constructor
  · apply (normal_subgroupOf_iff_le_normalizer hR).mpr
    rw [hs]
    exact sup_le R.le_normalizer ((le_centralizer_iff.mp hcomm).trans (centralizer_le_normalizer _))
  · apply (normal_subgroupOf_iff_le_normalizer hX).mpr
    rw [hs]
    exact sup_le (hcomm.trans (centralizer_le_normalizer _)) X.le_normalizer

omit [Finite G] in
/-- A normal dihedral factor is contained in every Sylow two-subgroup of the product. -/
theorem first_factor_le_sylow (C R X:Subgroup G) (hR:R≤C) (hX:X≤C)
    (split:C≃*R×X)
    (hc:∀c:C,(c:G)=((split c).1:G)*((split c).2:G))
    (hcomm:R≤centralizer (X:Set G)) (eR:DihedralGroup 4≃*R) (S:Sylow 2 C) :
    R≤(S:Subgroup C).map C.subtype := by
  let := (split_factor_normal C R X hR hX split hc hcomm).1
  have hp:IsPGroup 2 (R.subgroupOf C) :=
    (IsPGroup.of_card (by rw [DihedralGroup.nat_card];norm_num : Nat.card (DihedralGroup 4)=2^3)).of_equiv
      (eR.trans (subgroupOfEquivOfLe hR).symm)
  have hh:=map_mono (f:=C.subtype) (hp.le_sylow_of_normal S)
  rwa [map_subgroupOf_eq_of_le hR] at hh

/-- A Sylow of the S₄ factor is literally the intersection with the given Sylow. -/
theorem second_factor_sylow (C R X:Subgroup G) (hR:R≤C) (hX:X≤C)
    (split:C≃*R×X)
    (hc:∀c:C,(c:G)=((split c).1:G)*((split c).2:G))
    (hcomm:R≤centralizer (X:Set G)) (S:Sylow 2 C) :
    ∃P:Sylow 2 X, (P:Subgroup X).map X.subtype=
      ((S:Subgroup C).map C.subtype)⊓X := by
  let := (split_factor_normal C R X hR hX split hc hcomm).2
  obtain ⟨P,hP⟩:=S.exists_subgroupOf_eq_of_normal (X.subgroupOf C)
  let e : X.subgroupOf C≃*X := subgroupOfEquivOfLe hX
  refine ⟨P.mapSurjective (f:=e.toMonoidHom) (show Function.Surjective e.toMonoidHom from e.surjective),?_⟩
  rw [Sylow.coe_mapSurjective,map_map,hP]
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨⟨y.val,hy,rfl⟩,y.property⟩
  · rintro ⟨⟨y,hy,he⟩,hx⟩
    refine ⟨⟨y,by change C.subtype y∈X; rw [he]; exact hx⟩,hy,?_⟩
    exact he

end DihedralSymmetricFour

namespace DihedralSymmetricFour
open Subgroup
variable {X:Type*} [Group X] [Finite X]

/-- Every supplied Sylow in an actual S₄ factor has a dihedral coordinate system. -/
theorem sylow_dihedral (eX:X≃*Equiv.Perm (Fin 4)) (P:Sylow 2 X) :
    Nonempty (DihedralGroup 4≃*P) := by
  let Q:=P.mapSurjective (f:=eX.toMonoidHom)
    (show Function.Surjective eX.toMonoidHom from eX.surjective)
  let e : P≃*Q := (P:Subgroup X).equivMapOfInjective eX.toMonoidHom eX.injective
  obtain ⟨eQ⟩:=Equiv.Perm.sylow_two_equiv_dihedral_four Q
  exact ⟨(e.trans eQ).symm⟩
variable {G:Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A central element of the second factor's Sylow is central in the full Sylow. -/
theorem second_sylow_center (C R X:Subgroup G) (_hR:R≤C) (_hX:X≤C)
    (split:C≃*R×X)
    (hc:∀c:C,(c:G)=((split c).1:G)*((split c).2:G))
    (hcomm:R≤centralizer (X:Set G)) (S:Sylow 2 C)
    (hRS:R≤(S:Subgroup C).map C.subtype)
    (P:Sylow 2 X) (hP:(P:Subgroup X).map X.subtype=(S:Subgroup C).map C.subtype⊓X)
    (eP:DihedralGroup 4≃*P) :
    let u:G := ((eP (.r 2):P):X)
    ∀y∈(S:Subgroup C).map C.subtype,y*u=u*y := by
  dsimp only
  intro y hy
  let c:C := ⟨y,map_subtype_le _ hy⟩
  let r:R := (split c).1
  let x:X := (split c).2
  have he : y=(r:G)*(x:G) := hc c
  have hxS : (x:G)∈(S:Subgroup C).map C.subtype := by
    have hx : (x:G)=(r:G)⁻¹*y := by rw [he,inv_mul_cancel_left]
    rw [hx]
    exact mul_mem (inv_mem (hRS r.property)) hy
  have hxP : x∈(P:Subgroup X) := by
    have hh : (x:G)∈(P:Subgroup X).map X.subtype := hP ▸ ⟨hxS,x.property⟩
    obtain ⟨a,ha,he⟩:=hh
    exact (Subtype.ext he : a=x) ▸ ha
  have huR : (r:G)*(((eP (.r 2):P):X):G)=(((eP (.r 2):P):X):G)*(r:G) :=
    (mem_centralizer_iff.mp (hcomm r.property) _ ((eP (.r 2):X).property)).symm
  have huX : (x:G)*(((eP (.r 2):P):X):G)=(((eP (.r 2):P):X):G)*(x:G) := by
    have hh: (⟨x,hxP⟩:P)*(eP (.r 2))=(eP (.r 2))*(⟨x,hxP⟩:P) := by
      obtain ⟨a,ha⟩:=eP.surjective ⟨x,hxP⟩
      rw [←ha,←map_mul,←map_mul]
      exact congrArg eP (by
        exact (by decide +kernel : ∀a:DihedralGroup 4,a*.r 2=.r 2*a) a)
    exact congrArg (fun a:P=>((a:X):G)) hh
  rw [he,mul_assoc,huX,←mul_assoc,huR,mul_assoc]

end DihedralSymmetricFour
