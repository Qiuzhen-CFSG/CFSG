module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.Relations
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations.WeylGeometry
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations.BlockProduct
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations.ShortCommutators
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations.LongCommutators

/-!
# Matrix inputs to normal generation of the Suzuki-side Ree radical

The middle Weyl word is twist-fixed, belongs to the split Suzuki seed, and
conjugates the eighth named root curve to the second with the same parameter.
The fourth root curve is additive, and the third block satisfies the exact
main-parameter product law. Together with the five right-commutator calculations,
these prove all seven equations of `RootRelations` for the actual split F₄
matrix words. The Weyl geometry, block product and commutators are proved in
the corresponding imported modules; this module assembles the literal equations.

The source exponent `2θ` is `titsEnd`, and the commutator is
`a⁻¹ * b⁻¹ * a * b`. The equations retain the source factor order, including
the inverse third-root factor in the two long commutators. All identities hold
for every `m`, including zero.

Source: GLS3, 2.3.8, Table 2.4 and 2.4.5(d),
`refs/KGroup/GLS3/chapter2.tex`; Aschbacher–Smith F.1.12(II)(i), pp.263–264.
-/

public section
namespace ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration

/-- The third-block multiplication law, with precisely the central parameter
used in the source normal-generation argument. -/
theorem rootWord_third_mul (m : ℕ) (t u : CoefficientField m) :
    rootWord m 2 t * rootWord m 2 u =
      rootWord m 2 (t + u) * centralWord m 2 (titsEnd m t * u) :=
  MatrixRelations.rootWord_even_mul m 2 (by decide) t u

/-- The seven source root identities hold for the concrete split F₄ matrix words. -/
theorem rootWord_relations (m : ℕ) :
    RootRelations m (rootWord m) (centralWord m) :=
  ⟨rootWord_fourth_add m, rootWord_third_mul m,
    rootWord_second_eighth_commutator m, rootWord_first_fourth_commutator m,
    rootWord_first_sixth_commutator m, rootWord_first_eighth_commutator m,
    rootWord_first_seventh_commutator m⟩

end ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
