module
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus
/-!
# Irreducibility of the full binary plus orthogonal action

The full O4+(2) model is S3 wreath C2 on two anisotropic binary planes.
A nonzero invariant subspace contains a nonzero vector on one plane: move
one nonzero coordinate by a plane permutation and take the difference.
The plane permutations generate that coordinate plane, and swapping the
planes gives the other. Hence the subspace is all of V.

Source: Aschbacher--Smith 2.4.29, printed p.545.
-/
public section
namespace BinaryFourPlus
private theorem exists_nonzeroVector : ∀v : Plane,v≠0→∃i : Fin 3,nonzeroVector i=v := by decide
private theorem plane_move (v : Plane) (hv : v≠0) :
    ∃ a : Equiv.Perm (Fin 3), planeLinear a v≠v := by
  obtain ⟨i,hiv⟩ := exists_nonzeroVector v hv
  obtain ⟨j,hj⟩ := exists_ne i
  refine ⟨Equiv.swap i j,?_⟩
  rw [←hiv,planeLinear_nonzeroVector,Equiv.swap_apply_left]
  exact fun h=>hj (nonzeroVector_injective h)
private theorem plane_transitive (v w : Plane) (hv : v≠0) (hw : w≠0) :
    ∃a : Equiv.Perm (Fin 3),planeLinear a v=w := by
  obtain ⟨i,hiv⟩ := exists_nonzeroVector v hv
  obtain ⟨j,hjw⟩ := exists_nonzeroVector w hw
  refine ⟨Equiv.swap i j,?_⟩
  rw [←hiv,planeLinear_nonzeroVector,Equiv.swap_apply_left,hjw]

private def firstActor (a : Equiv.Perm (Fin 3)) : Wreath :=
  ⟨fun i=>if i=1 then a else 1,1⟩
private def swapActor : Wreath := RegularWreathProduct.inl swapIndex
private theorem firstActor_apply (a : Equiv.Perm (Fin 3)) (v : V) :
    (wreathToIsometry (firstActor a)).val v=(planeLinear a v.1,v.2) := by
  rw [wreathToIsometry_apply]
  simp [firstActor,swapIndex_ne_one]
private theorem swapActor_apply (v : V) :
    (wreathToIsometry swapActor).val v=(v.2,v.1) := by
  rw [wreathToIsometry_apply]
  simp [swapActor,swapIndex_ne_one]

theorem invariant_submodule_eq_bot_or_top (A : Submodule (ZMod 2) V)
    (hA : ∀w : Wreath,∀v∈A,(wreathToIsometry w).val v∈A) : A=⊥ ∨ A=⊤ := by
  by_cases hzero : A=⊥
  · exact Or.inl hzero
  right
  obtain ⟨v,hv,hv0⟩ := A.ne_bot_iff.mp hzero
  have hx : ∃u : Plane,u≠0 ∧ (u,0)∈A := by
    have step (v : V) (hv : v∈A) (h1 : v.1≠0) : ∃u : Plane,u≠0 ∧ (u,0)∈A := by
      obtain ⟨a,ha⟩ := plane_move v.1 h1
      have hm := hA (firstActor a) v hv
      rw [firstActor_apply] at hm
      refine ⟨planeLinear a v.1-v.1,sub_ne_zero.mpr ha,?_⟩
      have hh := A.sub_mem hm hv
      simpa only [Prod.sub_def,sub_self] using hh
    by_cases h1 : v.1=0
    · have h2 : v.2≠0 := by intro h;exact hv0 (Prod.ext h1 h)
      have hm := hA swapActor v hv
      rw [swapActor_apply] at hm
      exact step _ hm h2
    · exact step v hv h1
  obtain ⟨u,hu,huA⟩ := hx
  have haxis (w : Plane) : (w,0)∈A := by
    by_cases hw : w=0
    · subst w;exact A.zero_mem
    obtain ⟨a,ha⟩ := plane_transitive u w hu hw
    have hh := hA (firstActor a) (u,0) huA
    rwa [firstActor_apply,ha] at hh
  apply top_unique
  intro v _
  have hh := hA swapActor (v.2,0) (haxis v.2)
  rw [swapActor_apply] at hh
  simpa only [Prod.mk_add_mk,add_zero,zero_add] using A.add_mem (haxis v.1) hh
end BinaryFourPlus
