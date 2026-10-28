module

public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.LinearRadical.Levi
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.LinearRadical.TorusDetection.OddAction
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.LinearRadical.TorusDetection.Characters

/-!
# Faithful fixed-torus action on the linear Ree radical abelianization

For the specified linear radical R, the full fixed torus acts faithfully on
R/[R,R]. An element acting trivially belongs, through its conjugation action,
to the two-group kernel on the Frattini quotient. Its odd order forces it to
centralize R. Actual fixed radical words then separate the diagonal root
characters and force the torus element to be identity.

This discharges the torus-detection input in the linear-radical centralizer
argument, without a simplicity hypothesis or an additional action premise.
Source: GLS3, Theorem 2.6.5(e), `refs/KGroup/GLS3/chapter2.tex`.
-/

namespace ReeF4.SectionGeometry.LinearRadical

/-- The full fixed torus acts faithfully on the specified linear radical's
abelianization. The action condition uses the radical's own commutator subgroup. -/
public theorem fixedTorus_eq_one_of_trivial_radical_abelianization
    (m : ℕ) (_hm : 1 ≤ m) (t : Model m) (ht : t ∈ Parabolics.fixedTorus m)
    (ha : ActsTriviallyOnRadicalAbelianization m t) : t = 1 :=
  fixedTorus_eq_one_of_centralizes_radical m t ht
    (fixedTorus_centralizes_radical_of_trivial_abelianization m t ht ha)

end ReeF4.SectionGeometry.LinearRadical
