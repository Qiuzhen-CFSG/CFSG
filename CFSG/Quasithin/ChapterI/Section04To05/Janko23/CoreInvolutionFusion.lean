module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.LocalActionFusion
public import Theory.SpecificGroups.MinusExtraspecial.Factors
public import Theory.GroupTheory.QuaternionDihedralInvolutionCosets
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# Involution fusion in the Janko centralizer core

The literal action of H = C_G(z) on the five nonidentity singular cosets of
Q = F*(H) has kernel Q. Its image therefore has order sixty. A five-cycle
fuses the cosets, and inner conjugation fuses the two involutions in each
coset. The returning conjugate from `HTypeAt` then puts every involution of
Q in the ambient conjugacy class of z.

This proves the w = 2 case of Aschbacher, *Sporadic Groups* (1994),
46.1(2), printed p.251, directly from the exact I.4.7 local hypotheses.
It does not need simplicity or an assumption about the other involution class.
The separate outside-core calculation is 46.11, printed p.255.
-/

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Janko23

variable {G : Type*} [Group G] [Finite G] {z : G}

private theorem quotientAut_kernel_congr {Q : Type*} [Group Q]
    (U V : Subgroup Q) [U.Characteristic] [V.Characteristic] (h : U = V) :
    (quotientAut U).ker = (quotientAut V).ker := by
  subst V
  rfl

namespace HTypeAt

/-- The five singular points are the actual central involution cosets of the local core. -/
public theorem core_involution_cosets_card (h : HTypeAt z) :
    Nat.card (CentralInvolutionCosets (localCore z)) = 5 := by
  let := h.core_isExtraspecial
  obtain ⟨B, C, hB, hC, hcomm, hgen⟩ :=
    MinusExtraspecial.factors_of_equiv h.core_equiv.some
  exact quaternion_dihedral_central_involution_cosets_card h.core_card B C hB hC hcomm hgen

/-- The action on the five singular points has precisely the core as its kernel. -/
public theorem core_involution_action_kernel (h : HTypeAt z) :
    ((centralInvolutionCosetAction (H := localCore z)).comp
      (MulAut.conjNormal : involutionCentralizer z →* MulAut (localCore z))).ker =
        localCore z := by
  let := h.core_isExtraspecial
  obtain ⟨B, C, hB, hC, hcomm, hgen⟩ :=
    MinusExtraspecial.factors_of_equiv h.core_equiv.some
  rw [← MonoidHom.comap_ker,
    quaternion_dihedral_central_involution_coset_kernel B C hB hC hcomm hgen,
    ← quotientAut_kernel_congr (frattini (localCore z)) (center (localCore z))
      IsExtraspecial.frattini_eq_center_two,
    MonoidHom.comap_ker]
  exact h.coreFrattiniAction_kernel

/-- The noncentral core involutions form one class inside the full centralizer. -/
public theorem core_noncentral_involutions_isConj (h : HTypeAt z)
    (x y : localCore z) (hx : orderOf x = 2) (hxZ : x ∉ center (localCore z))
    (hy : orderOf y = 2) (hyZ : y ∉ center (localCore z)) :
    IsConj (x : involutionCentralizer z) (y : involutionCentralizer z) := by
  let := h.core_isExtraspecial
  apply isConj_noncentral_involutions_of_five_cosets (localCore z)
    h.core_involution_cosets_card ?_ x y hx hxZ hy hyZ
  rw [← index_ker, h.core_involution_action_kernel]
  change 5 ∣ Nat.card (involutionCentralizer z ⧸ localCore z)
  rw [h.quotient_card]
  decide

private theorem core_central_involution_eq (h : HTypeAt z)
    (x : localCore z) (hx : orderOf ((x : involutionCentralizer z) : G) = 2)
    (hxZ : x ∈ center (localCore z)) : ((x : involutionCentralizer z) : G) = z := by
  let e : localCore z ≃* ambientCore z := (localCore z).equivMapOfInjective
    (involutionCentralizer z).subtype (involutionCentralizer z).subtype_injective
  have heZ : e x ∈ center (ambientCore z) := by
    rw [mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := e.surjective q
    exact (e.map_mul y x).symm.trans
      ((congrArg e (mem_center_iff.mp hxZ y)).trans (e.map_mul x y))
  have hxline : ((x : involutionCentralizer z) : G) ∈ zpowers z :=
    h.core_center_image ▸ mem_map_of_mem (ambientCore z).subtype heZ
  exact congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two
    (x := (⟨((x : involutionCentralizer z) : G), hxline⟩ : zpowers z))
    (y := (⟨z, mem_zpowers z⟩ : zpowers z))
    ((orderOf_coe _).symm.trans hx) ((orderOf_coe _).symm.trans h.involution))

/-- Every involution of the core is an ambient conjugate of the distinguished involution. -/
public theorem core_involution_isConj (h : HTypeAt z) {u : G}
    (huQ : u ∈ ambientCore z) (hu : orderOf u = 2) : IsConj z u := by
  obtain ⟨uH, huQ, rfl⟩ := huQ
  let uQ : localCore z := ⟨uH, huQ⟩
  by_cases huZ : uQ ∈ center (localCore z)
  · have he : (uH : G) = z := h.core_central_involution_eq uQ hu huZ
    change IsConj z (uH : G)
    rw [he]
  obtain ⟨t, htQ, hzt, htz⟩ := h.exists_returning_conjugate
  obtain ⟨tH, htQ, rfl⟩ := htQ
  let tQ : localCore z := ⟨tH, htQ⟩
  have ht : orderOf (tH : G) = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hzt
    exact (congrArg orderOf hg).symm.trans
      (((MulAut.conj g).orderOf_eq z).trans h.involution)
  have htZ : tQ ∉ center (localCore z) := fun hc =>
    htz (h.core_central_involution_eq tQ ht hc)
  have htQ2 : orderOf tQ = 2 := by
    simpa only [← orderOf_coe] using ht
  have huQ2 : orderOf uQ = 2 :=
    (orderOf_coe uQ).symm.trans ((orderOf_coe uH).symm.trans hu)
  exact hzt.trans ((involutionCentralizer z).subtype.map_isConj
    (h.core_noncentral_involutions_isConj tQ uQ htQ2 htZ huQ2 huZ))

end HTypeAt
end CFSG.Quasithin.Janko23
