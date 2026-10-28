module

public import Theory.SpecificGroups.HaradaNorton.Simplicity.Reduction
public import Theory.SpecificGroups.HaradaNorton.Simplicity.WordCertificates
public import Theory.SpecificGroups.HaradaNorton.Simplicity.Center

/-!
# Simplicity reduction for the fixed Harada–Norton matrix group

Two explicit ATLAS word identities prove perfectness and normal generation by
`a`. A maximal centralizer of `a` and a trivial ambient center then prove
simplicity by the elementary normal-subgroup argument in
`NormalGeneratorCentralizerSimplicity`. A local center bound
`Z(C(a)) ⊆ {1,a}` is an alternative sufficient condition for centerlessness.

The checked word and commutant certificates give unconditional perfectness,
normal generation by `a`, and centerlessness. Thus `simple_of_maximal_centralizer`
has only maximality of `C(a)` left as a premise. This module does not yet assert
simplicity of the fixed matrices: maximality must still be proved for this
construction, and neither the ATLAS name nor its claimed order supplies it.

The proposed centralizer is the `2.HS.2` maximal subgroup of index 1539000 on
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/HN/. Matrix source attribution is
recorded in `MatrixSources.md`.
-/

namespace HaradaNorton

/-- Simplicity from two concrete word identities, maximality of `C(a)`, and
triviality of the ambient center. -/
public theorem simple_of_relations_maximal_centralizer_and_center
    (hab : (a * b) ^ 22 = 1) (hw : perfectWord ^ 25 = 1)
    (hmax : IsCoatom generatorCentralizer)
    (hcenter : Subgroup.center HN = ⊥) : IsSimpleGroup HN := by
  let := isPerfect_of_relations hab hw
  exact Subgroup.isSimpleGroup_of_normal_generator_maximal_centralizer
    (normal_eq_top_of_a_mem hab) hmax hcenter

/-- Simplicity from two concrete word identities and the two local centralizer
facts. This also exposes the alternative local center criterion. -/
public theorem simple_of_relations_and_centralizer
    (hab : (a * b) ^ 22 = 1) (hw : perfectWord ^ 25 = 1)
    (hmax : IsCoatom generatorCentralizer)
    (hcenter : ∀ z : generatorCentralizer, z ∈ Subgroup.center generatorCentralizer →
      (z : HN) = 1 ∨ (z : HN) = a) : IsSimpleGroup HN := by
  let := isPerfect_of_relations hab hw
  exact Subgroup.isSimpleGroup_of_normal_generator_centralizer
    (normal_eq_top_of_a_mem hab) hmax hcenter

/-- The certified ATLAS word identities prove perfectness of the fixed group. -/
public theorem isPerfect : Group.IsPerfect HN :=
  isPerfect_of_relations ab_pow_twenty_two perfectWord_pow_twenty_five

/-- The standard involution normally generates the fixed matrix group. -/
public theorem normal_eq_top_of_generator_mem
    (N : Subgroup HN) [N.Normal] (ha : a ∈ N) : N = ⊤ :=
  normal_eq_top_of_a_mem ab_pow_twenty_two N ha

/-- The fixed matrix group has trivial center. -/
public theorem center_eq_bot : Subgroup.center HN = ⊥ := by
  let := isPerfect
  exact center_eq_bot_of_isPerfect

/-- With the concrete word and center certificates discharged, maximality of
the involution centralizer is the remaining simplicity obligation. -/
public theorem simple_of_maximal_centralizer
    (hmax : IsCoatom generatorCentralizer) : IsSimpleGroup HN :=
  simple_of_relations_maximal_centralizer_and_center
    ab_pow_twenty_two perfectWord_pow_twenty_five hmax center_eq_bot

end HaradaNorton
