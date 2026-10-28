module
public import Theory.GroupAction.CosetTransport

/-!
# Equivariant coordinates on a marked orbit

An isomorphism taking the stabilizer of a point to a specified subgroup
identifies its orbit with the literal quotient by that subgroup. The formulas
retain the group action and the base point. Equivariant equivalences also
transport stabilizers and all subgroup-orbit cardinalities.

Application: the common native coordinates in Aschbacher–Smith J.5.13.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace MulAction
variable {G K X:Type*} [Group G] [Group K] [MulAction G X]
variable (e:G≃*K) (x:X) (H:Subgroup K) (h:(stabilizer G x).map e.toMonoidHom=H)

def markedOrbitEquiv : orbit G x≃K⧸H :=
  (orbitEquivQuotientStabilizer G x).trans
    ((cosetEquivMap e (stabilizer G x)).trans (quotientEquivOfEq h))

theorem markedOrbitEquiv_apply_smul (g:G) :
    markedOrbitEquiv e x H h ⟨g•x,mem_orbit x g⟩=(e g:K⧸H) := by
  have hh:(orbitEquivQuotientStabilizer G x) ⟨g•x,mem_orbit x g⟩=
      (g:G⧸stabilizer G x):=by
    apply (orbitEquivQuotientStabilizer G x).symm.injective
    rw [Equiv.symm_apply_apply]
    exact Subtype.ext (orbitEquivQuotientStabilizer_symm_apply G x g).symm
  change (quotientEquivOfEq h)
    ((cosetEquivMap e (stabilizer G x))
      ((orbitEquivQuotientStabilizer G x) ⟨g•x,mem_orbit x g⟩))=_
  rw [hh]
  rfl

theorem markedOrbitEquiv_smul (g:G) (v:orbit G x) :
    markedOrbitEquiv e x H h (g•v)=e g•markedOrbitEquiv e x H h v := by
  obtain ⟨k,hk⟩:=v.property
  have hv:v=⟨k•x,mem_orbit x k⟩:=Subtype.ext hk.symm
  subst v
  have he:g•(⟨k•x,mem_orbit x k⟩:orbit G x)=⟨(g*k)•x,mem_orbit x (g*k)⟩:=
    Subtype.ext (mul_smul _ _ _).symm
  rw [he,markedOrbitEquiv_apply_smul,markedOrbitEquiv_apply_smul,map_mul]
  rfl

theorem markedOrbitEquiv_base :
    markedOrbitEquiv e x H h ⟨x,mem_orbit_self x⟩=(1:K) := by
  simpa only [one_smul,map_one] using markedOrbitEquiv_apply_smul e x H h 1

variable {Y:Type*} [MulAction K Y] (f:X≃Y) (hf:∀g x,f (g•x)=e g•f x)

include hf in
theorem stabilizer_map_of_equivariant (x:X) :
    (stabilizer G x).map e.toMonoidHom=stabilizer K (f x) := by
  ext k
  obtain ⟨g,rfl⟩:=e.surjective k
  rw [mem_map_equiv, e.symm_apply_apply]
  change (g•x=x) ↔ (e g•f x=f x)
  rw [←hf,f.injective.eq_iff]

def orbitEquivOfEquivariant (P:Subgroup G) (x:X) :
    orbit P x ≃ orbit (P.map e.toMonoidHom) (f x) :=
  f.subtypeEquiv (fun y=>by
    constructor
    · rintro ⟨p,hp⟩
      refine ⟨⟨e p,mem_map_of_mem e.toMonoidHom p.property⟩,?_⟩
      exact (hf p x).symm.trans (congrArg f hp)
    · rintro ⟨p,hp⟩
      obtain ⟨g,hg,he⟩:=p.property
      refine ⟨⟨g,hg⟩,f.injective ?_⟩
      change f (g•x)=f y
      rw [hf]
      exact (congrArg (fun k:K=>k•f x) he).trans hp)

include hf in
theorem orbit_card_of_equivariant (P:Subgroup G) (x:X) :
    Nat.card (orbit P x)=Nat.card (orbit (P.map e.toMonoidHom) (f x)) :=
  Nat.card_congr (orbitEquivOfEquivariant e f hf P x)
end MulAction

namespace MulAction
variable {G X:Type*} [Group G] [MulAction G X]

def orbitSubtypeEquiv (P:Subgroup G) {b:X} (v:orbit G b) :
    orbit P v ≃ orbit P v.val where
  toFun w:=⟨w.val.val,mem_subgroup_orbit_iff.mp w.property⟩
  invFun w:=⟨⟨w.val,by
    obtain ⟨k,hk⟩:=w.property
    obtain ⟨a,ha⟩:=v.property
    refine ⟨(k:G)*a,?_⟩
    change ((k:G)*a)•b=w.val
    change a•b=v.val at ha
    rw [mul_smul,ha]
    exact hk⟩,mem_subgroup_orbit_iff.mpr w.property⟩
  left_inv _:=rfl
  right_inv _:=rfl

theorem orbitSubtype_card (P:Subgroup G) {b:X} (v:orbit G b) :
    Nat.card (orbit P v)=Nat.card (orbit P v.val) :=
  Nat.card_congr (orbitSubtypeEquiv P v)

theorem stabilizer_orbitSubtype {b:X} (v:orbit G b) :
    stabilizer G v=stabilizer G v.val := by
  ext k
  change k•v=v ↔ (k:G)•v.val=v.val
  exact Subtype.ext_iff
end MulAction
namespace MulAction
variable {G X:Type*} [Group G] [MulAction G X]
theorem suborbit_card_smul (g:G) (x y:X) :
    Nat.card (orbit (stabilizer G (g•x)) (g•y))=
      Nat.card (orbit (stabilizer G x) y) := by
  let f: X≃X:=MulAction.toPerm g
  have hf:∀k z,f (k•z)=(MulAut.conj g) k•f z:=by
    intro k z
    change g•(k•z)=(g*k*g⁻¹)•(g•z)
    simp only [mul_smul,inv_smul_smul]
  have hh:=orbit_card_of_equivariant (MulAut.conj g) f hf (stabilizer G x) y
  have hs:=stabilizer_map_of_equivariant (MulAut.conj g) f hf x
  rw [hs] at hh
  exact hh.symm
end MulAction
