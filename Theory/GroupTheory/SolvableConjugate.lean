module

public import Mathlib.GroupTheory.Solvable

/-!
# Solvability of subgroups conjugate into solvable subgroups

Conjugation restricts to an injective homomorphism into the target subgroup,
so solvability pulls back. Both orientations of conjugate containment are
provided for subgroup recognition arguments.
-/

namespace Group

/-- A subgroup whose conjugate lies in a solvable subgroup is solvable. -/
public theorem isSolvable_of_conjugate_le
    {G : Type*} [Group G] (H K : Subgroup G) [IsSolvable K]
    (g : G) (h : H.map (MulAut.conj g).toMonoidHom ≤ K) : IsSolvable H := by
  let f : H →* K := ((MulAut.conj g).toMonoidHom.comp H.subtype).codRestrict K
    (fun x => h (Subgroup.mem_map.mpr ⟨x, x.property, rfl⟩))
  exact isSolvable_of_isSolvable_injective (f := f)
    (fun x y he => Subtype.ext ((MulAut.conj g).injective (congrArg Subtype.val he)))

/-- Every subgroup of a conjugate of a solvable subgroup is solvable. -/
public theorem isSolvable_of_le_conjugate
    {G : Type*} [Group G] (H K : Subgroup G) [IsSolvable K]
    (g : G) (h : H ≤ K.map (MulAut.conj g).toMonoidHom) : IsSolvable H := by
  let e := K.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  let : IsSolvable (K.map (MulAut.conj g).toMonoidHom) :=
    isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  exact isSolvable_of_isSolvable_injective (f := Subgroup.inclusion h)
    (Subgroup.inclusion_injective h)

end Group
