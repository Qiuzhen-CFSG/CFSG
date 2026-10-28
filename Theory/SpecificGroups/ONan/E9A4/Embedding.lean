module

public import Theory.SpecificGroups.ONan.E9A4.MatrixTable
public import Theory.SpecificGroups.ONan.E9A4.WordMatrices

/-!
# An E₉ × A₄ subgroup of the projective O'Nan model

The checked word matrices discharge the realization premise of the projective
transition table. Its 108 distinct normal forms therefore give an injective
homomorphism from the actual product of two cyclic groups of order three and
the alternating group on four points to `ONan.Model`.

The nontrivial transition scalars disappear in the projective quotient; the
construction does not assert an embedding in the linear triple cover. No order
or simplicity theorem for O'Nan is needed.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, A.2.19,
printed p. 41 (PDF p. 52), which obtains this subgroup inside E₉ × A₆.
The concrete matrix and word sources are recorded in `source/README.md`.
-/

public section
namespace ONan.E9A4

open Theory.SpecificGroups.E9A4 (Source Coord next)

/-- The actual projective words satisfy every source-group generator transition. -/
theorem normalForm_next (c : Coord) (i : Fin 4) :
    normalForm (next c i) = normalForm c * generators i :=
  normalForm_next_of_realization linearGenerators_matrix c i

/-- The 108 actual projective normal forms are pairwise distinct. -/
theorem normalForm_injective : Function.Injective normalForm :=
  normalForm_injective_of_realization linearGenerators_matrix

/-- The concrete E₉ × A₄ homomorphism into the projective O'Nan model. -/
noncomputable def embedding : Source →* Model :=
  Theory.SpecificGroups.E9A4.homOfTransitions generators normalForm_next

/-- The concrete homomorphism is an embedding, without additional premises. -/
theorem embedding_injective : Function.Injective embedding :=
  Theory.SpecificGroups.E9A4.homOfTransitions_injective
    generators normalForm_next normalForm_injective

end ONan.E9A4
