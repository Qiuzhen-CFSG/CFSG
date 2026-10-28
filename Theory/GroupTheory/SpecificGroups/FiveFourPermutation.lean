module

public import Theory.GroupTheory.SpecificGroups.FiveFour
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# The five-point affine action of C₅:C₄

Translation and the faithful multiplicative action give an embedding in
S₅. This supplies the actual subgroup used to restrict a faithful S₅
action on an elementary abelian group of order sixteen.
-/

@[expose] public noncomputable section
namespace FiveFour

def affineHom : Group →* Equiv.Perm (Cyclic 5) where
  toFun g := Equiv.mulLeft g.left * (action g.right).toEquiv
  map_one' := by ext x; simp
  map_mul' g h := by
    ext x
    change (g.left * action g.right h.left) * action (g.right * h.right) x =
      g.left * action g.right (h.left * action h.right x)
    simp only [map_mul,MulAut.mul_apply,mul_assoc]

theorem affineHom_injective : Function.Injective affineHom := by
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  have hleft : g.left = 1 := by
    have hh := congrArg (fun p : Equiv.Perm (Cyclic 5) => p 1) hg
    simpa [affineHom] using hh
  have hright : g.right = 1 := by
    apply action_injective
    rw [map_one]
    ext x
    have hh := congrArg (fun p : Equiv.Perm (Cyclic 5) => p x) hg
    simpa [affineHom,hleft] using hh
  exact SemidirectProduct.ext hleft hright

/-- A faithful realization of the affine group in the literal S₅. -/
def permutationHom : Group →* Equiv.Perm (Fin 5) :=
  ((Fintype.equivFin (Cyclic 5)).permCongrHom).toMonoidHom.comp affineHom

theorem permutationHom_injective : Function.Injective permutationHom :=
  ((Fintype.equivFin (Cyclic 5)).permCongrHom).injective.comp affineHom_injective

end FiveFour
