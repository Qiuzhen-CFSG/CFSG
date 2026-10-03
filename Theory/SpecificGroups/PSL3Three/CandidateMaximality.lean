module

public import Theory.SpecificGroups.PSL3Three.LineMaximality
public import Theory.SpecificGroups.PSL3Three.PlaneMaximality
public import Theory.SpecificGroups.PSL3Three.MonomialMaximality
public import Theory.SpecificGroups.PSL3Three.SingerMaximality

/-!
# Maximality of the four concrete SL₃(3) candidates

The coordinate line stabilizer, coordinate plane stabilizer, irreducible
monomial subgroup and specified Singer normalizer are maximal proper
subgroups of the actual determinant-one matrix group. Each proof uses checked
coset coverage and explicit words recovering the ambient generators from any
outside double-coset representative. It is independent of proper-subgroup
completeness, subgroup orders and the classification of maximal subgroups.

The monomial candidate is precisely the subgroup preserving the six signed
coordinate vectors from `Subgroups`, not the other order-24 subgroup class.

Source: GLS III, Theorem 6.5.3(a–c), concrete maximal-subgroup constructions.
-/

namespace Matrix.PSL3Three

/-- All four specified matrix subgroups are maximal proper subgroups. -/
public theorem candidateSubgroups_isCoatom :
    IsCoatom lineStabilizerSL ∧ IsCoatom planeStabilizerSL ∧
      IsCoatom monomialSL ∧ IsCoatom singerNormalizerSL :=
  ⟨isCoatom_lineStabilizerSL, isCoatom_planeStabilizerSL,
    isCoatom_monomialSL, isCoatom_singerNormalizerSL⟩

end Matrix.PSL3Three
