module

public import Theory.SpecificGroups.Tits.FiniteImageOrder
public import Theory.SpecificGroups.Tits.Atlas1600Primitive
public import Theory.SpecificGroups.Tits.Atlas1600SylowTwo
public import Theory.SpecificGroups.Tits.Atlas1600NormalGenerator
public import Theory.GroupAction.PrimitiveSimplicity

/-!
# Simplicity of the concrete finite Parrott image

The faithful primitive action on 1600 points makes every nontrivial normal
subgroup transitive, hence of even order. The certified Sylow-two subgroup
then forces it to contain `r5`, whose normal closure is the whole group.
Thus the concrete quotient supplied by `FiniteImageOrder` is simple.

The permutation certificates use the Atlas data in
`refs/original/n-group-global/atlas-tits-p1600-{a,b}.g`; the normal-generator
argument uses Parrott (1972), §5, p. 683, transcribed in
`refs/original/n-group-global/parrott-tits-presentation.md`.
-/

namespace Tits

/-- The certified finite image of Parrott's presentation is simple. -/
public instance atlas1600_isSimpleGroup : IsSimpleGroup Atlas1600Group := by
  apply MulAction.isSimpleGroup_of_quasiprimitive_of_normal_card (X := Fin 1600)
    (d := 2) (by simp)
  intro N hN heven
  let : N.Normal := hN
  exact atlas1600_normal_eq_top_of_r5_mem N (atlas1600R5_mem_normal_of_even N heven)

end Tits
