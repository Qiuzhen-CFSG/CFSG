module
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.FiniteImage
import all Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.Plane

/-!
# The cubic residual of the prescribed orthogonal point stabilizer

In the binary plus four-space, the stabilizer of a nonzero second-axis vector
has order twelve and two-residual of order three. Its first-axis rotation moves
every nonzero first-axis vector. This is the literal marked action used to
construct Y=O²(C_H(v₂)) in Aschbacher–Smith10.2.1, printed p.743.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
open BinaryFourPlus
private instance : DecidableEq Wreath :=
  (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) C2).injective.decidableEq
private instance : Fintype Wreath := Fintype.ofEquiv _
  (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) C2).symm

@[expose] def pointStabilizer (v : V) : Subgroup Wreath where
  carrier := {g | (wreathToIsometry g).val v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change (wreathToIsometry (a*b)).val v=v
    rw [map_mul]
    change (wreathToIsometry a).val ((wreathToIsometry b).val v)=v
    rw [hb,ha]
  inv_mem' := by
    intro a ha
    change (wreathToIsometry a⁻¹).val v=v
    rw [map_inv]
    exact (wreathToIsometry a).val.symm_apply_eq.mpr ha.symm

private def cycle : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
private def rotation : Wreath := ⟨fun i => if i=1 then cycle else 1,1⟩
private def eval (w : Wreath) (v : V) : V :=
  if w.right=1 then (planeLinear (w.left 1) v.1,planeLinear (w.left swapIndex) v.2)
  else (planeLinear (w.left 1) v.2,planeLinear (w.left swapIndex) v.1)
private theorem eval_eq (w : Wreath) (v : V) : eval w v=(wreathToIsometry w).val v :=
  (wreathToIsometry_apply w v).symm
private theorem rotation_cube : rotation^3=1 := by decide +kernel
private theorem rotation_ne_one : rotation≠1 := by decide +kernel
private theorem rotation_fixes (b : Plane) :
    (wreathToIsometry rotation).val (0,b)=(0,b) := by
  rw [←eval_eq]
  exact (by decide +kernel : ∀b:Plane,eval rotation (0,b)=(0,b)) b
private theorem rotation_moves (a : Plane) (ha : a≠0) :
    (wreathToIsometry rotation).val (a,0)≠(a,0) := by
  rw [←eval_eq]
  exact (by decide +kernel : ∀a:Plane,a≠0→eval rotation (a,0)≠(a,0)) a ha

private theorem point_stabilizer_card (b : Plane) (hb : b≠0) :
    Nat.card (pointStabilizer (0,b))=12 := by
  have hh : ∀b:Plane,b≠0→Fintype.card {g:Wreath // eval g (0,b)=(0,b)}=12 := by
    decide +kernel
  change Nat.card {g:Wreath // (wreathToIsometry g).val (0,b)=(0,b)}=12
  simpa only [←eval_eq,Nat.card_eq_fintype_card] using hh b hb

private theorem rotation_conjugates (b : Plane) (hb : b≠0)
    (g : pointStabilizer (0,b)) :
    g.val*rotation*g.val⁻¹=rotation ∨ g.val*rotation*g.val⁻¹=rotation⁻¹ := by
  have hh : ∀b:Plane,b≠0→∀g:Wreath,eval g (0,b)=(0,b)→
      g*rotation*g⁻¹=rotation ∨ g*rotation*g⁻¹=rotation⁻¹ := by decide +kernel
  exact hh b hb g.val (by rw [eval_eq]; exact g.property)

theorem point_stabilizer_residual_card (b : Plane) (hb : b≠0) :
    Nat.card (pResidual 2 (pointStabilizer (0,b)))=3 := by
  let r : pointStabilizer (0,b) := ⟨rotation,rotation_fixes b⟩
  have ho : orderOf r=3 := orderOf_eq_prime
    (Subtype.ext rotation_cube) (fun he => rotation_ne_one (congrArg Subtype.val he))
  let R := zpowers r
  have hR : Nat.card R=3 := (Nat.card_zpowers r).trans ho
  have hnormal : R.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    intro g _
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    change zpowers ((MulAut.conj g) r)=R
    rcases rotation_conjugates b hb g with hh | hh
    · have he : (MulAut.conj g) r=r := Subtype.ext hh
      rw [he]
    · have he : (MulAut.conj g) r=r⁻¹ := Subtype.ext hh
      rw [he,zpowers_inv]
  let := hnormal
  have hi : R.index=4 := by
    have hh := R.card_mul_index
    rw [hR,point_stabilizer_card b hb] at hh
    omega
  have he : pResidual 2 (pointStabilizer (0,b))=R := by
    apply le_antisymm
    · apply sInf_le
      exact ⟨hnormal,IsPGroup.of_card (n:=2) (by change R.index=2^2; rw [hi]; decide)⟩
    · exact zpowers_le.mpr (mem_pResidual_of_orderOf_coprime (by rw [ho]; decide))
  rw [he,hR]

theorem exists_odd_point_stabilizer_moving (a b : Plane) (ha : a≠0) :
    ∃ r : pointStabilizer (0,b), r ∈ pResidual 2 (pointStabilizer (0,b)) ∧
      (wreathToIsometry r.val).val (a,0)≠(a,0) := by
  let r : pointStabilizer (0,b) := ⟨rotation,rotation_fixes b⟩
  have ho : orderOf r=3 := orderOf_eq_prime
    (Subtype.ext rotation_cube) (fun he => rotation_ne_one (congrArg Subtype.val he))
  exact ⟨r,mem_pResidual_of_orderOf_coprime (by rw [ho]; decide),rotation_moves a ha⟩
end CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
