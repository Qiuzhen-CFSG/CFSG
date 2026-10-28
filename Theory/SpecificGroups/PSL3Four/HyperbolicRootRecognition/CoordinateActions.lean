module

public import Theory.SpecificGroups.PSL3Four.HyperbolicRootRecognition.Coordinates

/-!
# The original automorphisms on the binary central quotient

The normal forms identify the center with the zero vector fiber. Every actual
automorphism therefore induces an additive map on the four binary quotient
coordinates. Its formula is extracted from the original action, and the
literal fixed-coset condition becomes a fixed-vector condition. No quotient
representation or shear formula is taken as an input.
Source: Aschbacher, *Sporadic Groups* (1994), proof of 45.3, pp.242–243.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace Theory.GroupTheory.HyperbolicRecognition
variable {K : Type*} [Group K] {F : HyperbolicFactors K}
    {P : HyperbolicFrame F.A F.z} {Q : HyperbolicFrame F.B F.u}
namespace MarkedCoordinates
variable (C : MarkedCoordinates F P Q)

/-- The actual center is exactly the zero quotient-vector fiber. -/
theorem center_mem (x : K) : x ∈ center K ↔ (C.equiv x).vector = 0 := by
  rw [← F.inf_eq, mem_inf, C.first_mem, C.second_mem]
  constructor
  · rintro ⟨h₂,h₁⟩
    exact Prod.ext h₁ h₂
  · intro h
    exact ⟨congrArg Prod.snd h, congrArg Prod.fst h⟩

/-- Conjugating coordinates retains the literal original automorphism. -/
def transport (a : MulAut K) : MulAut (Word C.matrix) :=
  C.equiv.symm.trans (a.trans C.equiv)

@[simp] theorem transport_apply (a : MulAut K) (w : Word C.matrix) :
    C.transport a w = C.equiv (a (C.equiv.symm w)) := rfl

private theorem transport_center_vector (a : MulAut K) (c : Central) :
    (C.transport a (centralWord C.matrix c)).vector = 0 := by
  have hc : C.equiv.symm (centralWord C.matrix c) ∈ center K := by
    apply (C.center_mem _).mpr
    rw [C.equiv.apply_symm_apply]
    rfl
  exact (C.center_mem _).mp ((centerCongr a) ⟨_,hc⟩).property

private theorem word_decomposition (w : Word C.matrix) :
    w = lift C.matrix w.vector * centralWord C.matrix w.central := by
  apply Word.ext
  · simp [lift,centralWord]
  · change w.central = 0 + w.central + cocycle C.matrix w.vector 0
    simp

private theorem transport_vector (a : MulAut K) (w : Word C.matrix) :
    (C.transport a w).vector = (C.transport a (lift C.matrix w.vector)).vector := by
  calc
    _ = (C.transport a (lift C.matrix w.vector * centralWord C.matrix w.central)).vector :=
      congrArg (fun x => (C.transport a x).vector) (C.word_decomposition w)
    _ = _ := by rw [map_mul,mul_vector,C.transport_center_vector,add_zero]

/-- The quotient map extracted from the actual source automorphism. -/
def quotientMap (a : MulAut K) : Vector →+ Vector where
  toFun v := (C.transport a (lift C.matrix v)).vector
  map_zero' := by
    change (C.transport a 1).vector = 0
    rw [map_one]
    rfl
  map_add' v w := by
    have h := congrArg Word.vector ((C.transport a).map_mul
      (lift C.matrix v) (lift C.matrix w))
    rw [C.transport_vector a (lift C.matrix v * lift C.matrix w)] at h
    exact h

/-- The induced map agrees with the original action on every representative. -/
theorem quotientMap_original (a : MulAut K) (x : K) :
    C.quotientMap a (C.equiv x).vector = (C.equiv (a x)).vector := by
  change (C.transport a (lift C.matrix (C.equiv x).vector)).vector = _
  rw [← C.transport_vector a (C.equiv x), C.transport_apply, C.equiv.symm_apply_apply]

/-- An actual involution remains involutory on the quotient coordinates. -/
theorem quotientMap_involutive (a : MulAut K) (ha : a ^ 2 = 1) :
    Function.Involutive (C.quotientMap a) := by
  intro v
  let x := C.equiv.symm (lift C.matrix v)
  have hx : (C.equiv x).vector = v := by simp [x,lift]
  rw [← hx,C.quotientMap_original,C.quotientMap_original]
  have hh : a (a x) = x := DFunLike.congr_fun ha x
  rw [hh]

/-- Fixed cosets under the original actor are exactly fixed quotient vectors. -/
theorem quotientMap_fixed_iff (a : MulAut K) (x : K) :
    C.quotientMap a (C.equiv x).vector = (C.equiv x).vector ↔
      a x * x⁻¹ ∈ center K := by
  rw [C.quotientMap_original,C.center_mem,map_mul,map_inv]
  change (C.equiv (a x)).vector = (C.equiv x).vector ↔
    (C.equiv (a x)).vector + (C.equiv x).vector = 0
  exact CharTwo.add_eq_zero.symm

/-- The first actual source reflection fixes precisely the first quotient plane. -/
theorem quotientMap_first_fixed (a : F.FirstActor) (v : Vector) :
    C.quotientMap a.aut v = v ↔ v.2 = 0 := by
  let x := C.equiv.symm (lift C.matrix v)
  have hx : (C.equiv x).vector = v := by simp [x,lift]
  rw [← hx,C.quotientMap_fixed_iff,a.fixed_iff,C.first_mem]

/-- The second actual source reflection fixes precisely the second quotient plane. -/
theorem quotientMap_second_fixed (a : F.SecondActor) (v : Vector) :
    C.quotientMap a.aut v = v ↔ v.1 = 0 := by
  let x := C.equiv.symm (lift C.matrix v)
  have hx : (C.equiv x).vector = v := by simp [x,lift]
  rw [← hx,C.quotientMap_fixed_iff,a.fixed_iff,C.second_mem]

end MarkedCoordinates
end Theory.GroupTheory.HyperbolicRecognition
