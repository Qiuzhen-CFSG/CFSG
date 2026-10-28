module
public import Theory.GroupAction.MarkedOrbit
/-!
# Equivariant comparison from a family of marked orbits

An isomorphism carrying each marked stabilizer to its counterpart gives
an equivariant bijection between the associated orbits. Disjoint families
of such orbits covering both sets then give an equivariant bijection of
the entire sets. The finite three-orbit application is Asc94,45.11.
-/
public section
open Subgroup
namespace MulAction
variable {G H X Y I:Type*} [Group G] [Group H] [MulAction G X] [MulAction H Y]

noncomputable def orbitEquivOfStabilizerMap (e:G≃*H) (x:X) (y:Y)
    (hs:(stabilizer G x).map e.toMonoidHom=stabilizer H y) : orbit G x ≃ orbit H y :=
  (markedOrbitEquiv e x (stabilizer H y) hs).trans (orbitEquivQuotientStabilizer H y).symm

theorem orbitEquivOfStabilizerMap_apply (e:G≃*H) (x:X) (y:Y)
    (hs:(stabilizer G x).map e.toMonoidHom=stabilizer H y) (g:G) :
    (orbitEquivOfStabilizerMap e x y hs ⟨g•x,mem_orbit x g⟩).val=e g•y := by
  change ((orbitEquivQuotientStabilizer H y).symm
    (markedOrbitEquiv e x (stabilizer H y) hs ⟨g•x,mem_orbit x g⟩)).val=_
  rw [markedOrbitEquiv_apply_smul]
  exact orbitEquivQuotientStabilizer_symm_apply H y (e g)

theorem orbit_family_equiv (e:G≃*H) (r:I→X) (s:I→Y)
    (hcoverX:∀x:X,∃(i:I)(g:G),g•r i=x) (hcoverY:∀y:Y,∃(i:I)(k:H),k•s i=y)
    (hsepX:∀i j:I,∀g k:G,g•r i=k•r j→i=j)
    (hsepY:∀i j:I,∀g k:H,g•s i=k•s j→i=j)
    (hst:∀i:I,(stabilizer G (r i)).map e.toMonoidHom=stabilizer H (s i)) :
    ∃F:X≃Y,(∀i:I,F (r i)=s i) ∧ ∀g:G,∀x:X,F (g•x)=e g•F x := by
  classical
  let dx : (Σi:I,orbit G (r i))→X := fun u=>u.2.val
  let dy : (Σi:I,orbit H (s i))→Y := fun u=>u.2.val
  have hdx : Function.Bijective dx := by
    constructor
    · rintro ⟨i,u⟩ ⟨j,v⟩ huv
      obtain ⟨g,hg⟩ := u.property
      obtain ⟨k,hk⟩ := v.property
      have hij : i=j := hsepX i j g k (hg.trans (huv.trans hk.symm))
      cases hij
      exact congrArg (Sigma.mk i) (Subtype.ext huv)
    · intro x
      obtain ⟨i,g,hg⟩ := hcoverX x
      exact ⟨⟨i,⟨g•r i,mem_orbit _ _⟩⟩,hg⟩
  have hdy : Function.Bijective dy := by
    constructor
    · rintro ⟨i,u⟩ ⟨j,v⟩ huv
      obtain ⟨g,hg⟩ := u.property
      obtain ⟨k,hk⟩ := v.property
      have hij : i=j := hsepY i j g k (hg.trans (huv.trans hk.symm))
      cases hij
      exact congrArg (Sigma.mk i) (Subtype.ext huv)
    · intro y
      obtain ⟨i,k,hk⟩ := hcoverY y
      exact ⟨⟨i,⟨k•s i,mem_orbit _ _⟩⟩,hk⟩
  let Ex := Equiv.ofBijective dx hdx
  let Ey := Equiv.ofBijective dy hdy
  let E := Equiv.sigmaCongrRight (fun i=>orbitEquivOfStabilizerMap e (r i) (s i) (hst i))
  let F := Ex.symm.trans (E.trans Ey)
  have hf (i:I) (g:G) : F (g•r i)=e g•s i := by
    have hx : Ex.symm (g•r i)=⟨i,⟨g•r i,mem_orbit _ _⟩⟩ :=
      Ex.symm_apply_eq.mpr rfl
    change Ey (E (Ex.symm (g•r i)))=_
    rw [hx]
    exact orbitEquivOfStabilizerMap_apply e (r i) (s i) (hst i) g
  refine ⟨F,?_,?_⟩
  · intro i
    simpa only [one_smul,map_one] using hf i 1
  · intro g x
    obtain ⟨i,k,rfl⟩ := hcoverX x
    rw [←mul_smul,hf,map_mul,mul_smul,←hf]
end MulAction
