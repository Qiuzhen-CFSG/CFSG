module
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# A normal intersection determines its point stabilizer

If the normalizer of a point stabilizer's intersection with a normal subgroup
is that point stabilizer, this intersection fixes no other point in the same
orbit. Equal cardinalities of conjugate intersections supply the key step.
The source Rudvalis application excludes the index-two socle exception in the
native thirteen-overgroup theorem.
-/

public noncomputable section
open Subgroup
namespace MulAction
variable {K Ω:Type*} [Group K] [Finite K] [MulAction K Ω]

theorem eq_of_stabilizer_normal_intersection_le (x y:Ω) (N:Subgroup K) [N.Normal]
    (hn:normalizer (stabilizer K x⊓N:Set K)=stabilizer K x)
    (hy:y∈orbit K x) (hxy:stabilizer K x⊓N≤stabilizer K y) : y=x := by
  obtain ⟨f,rfl⟩:=hy
  have he:(stabilizer K x⊓N).map (MulAut.conj f).toMonoidHom=
      stabilizer K (f•x)⊓N:=by
    rw [map_inf _ _ _ (MulAut.conj f).injective,←stabilizer_smul_eq_stabilizer_map_conj]
    exact congrArg (fun A:Subgroup K=>stabilizer K (f•x)⊓A) (Normal.map_conj_eq N f)
  have hle:stabilizer K x⊓N≤(stabilizer K x⊓N).map (MulAut.conj f).toMonoidHom:=by
    rw [he];exact le_inf hxy inf_le_right
  have heq:stabilizer K x⊓N=(stabilizer K x⊓N).map (MulAut.conj f).toMonoidHom:=
    eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj f).injective])
  have hf:f∈normalizer (stabilizer K x⊓N:Set K):=
    mem_normalizer_iff_map_conj_eq.mpr heq.symm
  exact hn.le hf
end MulAction
