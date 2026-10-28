module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Centralizer
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Intersection

/-!
# The concrete native linear-five elementary subgroup

This public leaf supplies the actual elementary subgroup F of order 1024 in
max1, its exact octad-kernel image, intersection of order 64 with E, and whole
ambient centralizer C(F)=F. Each of its four outside generators is an explicit
involution in Q outside E. The native word and matrix certificates are in the
imported leaves, with eleven-bit structural calculations used where possible.

Source: Kleidman--Wilson (1988), pp.485,490. Full normalizer recognition and the
two-global-conjugate occurrence geometry are separate remaining obligations;
none is inferred from the order of F or the ATLAS subgroup label.
-/

public noncomputable section
namespace Janko4.LocalStructure.LinearFive
open Cardinality Subgroup
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel

theorem lift_mem_F (i : Fin 4) : (lift i : Model) ∈ F := by
  simpa only [generators, Fin.append_right] using generator_mem_F (Fin.natAdd 6 i)

theorem lift_not_mem_E (i : Fin 4) : (lift i : Model) ∉ E := by
  rintro ⟨e, he, heq⟩
  have heq' : e = lift i := M.subtype_injective heq
  subst e
  apply projection_lift_ne_one i
  apply MonoidHom.mem_ker.mp
  rwa [MathieuHallActors.projection_ker]

theorem lift_order (i : Fin 4) : orderOf (lift i : Model) = 2 := by
  apply orderOf_eq_prime
  · rw [pow_two]
    exact congrArg (fun a : M => (a : Model)) (lift_square i)
  · intro h
    exact lift_not_mem_E i (h.symm ▸ E.one_mem)

/-- Four explicit witnesses for the outside-involution branch of the source. -/
theorem native_lift_spec (i : Fin 4) :
    (lift i : Model) ∈ Q ∧ (lift i : Model) ∉ E ∧ orderOf (lift i : Model) = 2 :=
  ⟨F_le_Q (lift_mem_F i), lift_not_mem_E i, lift_order i⟩

end Janko4.LocalStructure.LinearFive
