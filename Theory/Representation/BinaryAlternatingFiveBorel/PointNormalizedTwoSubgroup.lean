module
public import Theory.Representation.BinaryAlternatingFiveBorel.NormalizedTwoSubgroup

/-!
# Two-subgroups normalized by an arbitrary A₅ point Borel

Conjugating the chosen point to the standard fifth point transfers the
checked Borel calculation without changing the actual subgroup image.
Source application: Aschbacher--Smith preliminary15.2.23, p.1115.
-/

public section
open Subgroup
namespace BinaryPermutation.AlternatingFiveBorel
open Equiv

theorem even_point_stabilizer_normalizes_twoSubgroup
    (P : Subgroup (Perm (Fin 5))) (hP : IsPGroup 2 P) (i : Fin 5)
    (hN : alternatingGroup (Fin 5) ⊓ MulAction.stabilizer (Perm (Fin 5)) i ≤
      normalizer (P : Set (Perm (Fin 5)))) : P ≤ alternatingGroup (Fin 5) := by
  let s : Perm (Fin 5) := Equiv.swap i 4
  let c := MulAut.conj s
  have hc : Function.Injective c.toMonoidHom := c.injective
  have hN' (b : B) : borelToPerm b ∈ normalizer (P.map c.toMonoidHom : Set (Perm (Fin 5))) := by
    have hb : c.symm (borelToPerm b) ∈ alternatingGroup (Fin 5) ⊓
        MulAction.stabilizer (Perm (Fin 5)) i := by
      constructor
      · change (s⁻¹ * borelToPerm b * s).sign = 1
        simp only [map_mul,map_inv]
        have hh : (borelToPerm b).sign = 1 := b.val.property
        rw [hh,mul_one,inv_mul_cancel]
      · change s⁻¹ (borelToPerm b (s i)) = i
        simp only [s,Equiv.swap_apply_left,Equiv.swap_inv]
        have hh : borelToPerm b 4 = 4 := b.property
        rw [hh,Equiv.swap_apply_right]
    have hm := le_normalizer_map c.toMonoidHom (mem_map_of_mem c.toMonoidHom (hN hb))
    simpa only [MulEquiv.coe_toMonoidHom,c.apply_symm_apply] using hm
  intro a ha
  have hh := (normalizes_twoSubgroup_point_even (P.map c.toMonoidHom) (hP.map _)
    hN' (c a) (mem_map_of_mem _ ha)).2
  change a.sign = 1
  simpa only [c,MulAut.conj_apply,map_mul,map_inv,mul_comm,mul_left_comm,
    mul_inv_cancel_right] using hh
end BinaryPermutation.AlternatingFiveBorel
