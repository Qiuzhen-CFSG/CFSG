module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.PrimeDegree.Inputs
public import Theory.SpecificGroups.SU3.OddPrimeRootConfiguration

/-!
# The concrete root-geometry input to the odd PSU₃ degree bound

The actual projective matrix group contains a rational extraspecial
subgroup of order p³. The construction retains the arbitrary Hermitian
form and its prescribed prime Frobenius involution. This discharges
`PrimeDegreeRootGeometry`; the separate covering-center input and the
source degree assembly remain in `PrimeDegree`.

Sources: Huppert II.10.4 and II.10.12; Guralnick–Malle, *Classification of
2F-modules I*, Proposition 4.3; Aschbacher–Smith K.2, printed p.453.
-/

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion

/-- The unconditional concrete root configuration required by the local
rational-extraspecial degree argument. -/
public theorem primeDegreeRootGeometry : PrimeDegreeRootGeometry := by
  intro F _ _ J p hp _ hcard hconj
  exact J.hasRationalExtraspecialSubgroup_of_prime hp hcard hconj

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion
