module

public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.M11Exclusion.Inputs
public import Theory.Representation.Mathieu.SmallModules.M11DegreeTwelve
public import Theory.Representation.Mathieu.SmallModules.M11DegreeTwelve.Completeness

/-!
# The marked M11 recognition application

The concrete index-twelve overgroup of the marked eleven-normalizer and its
two coset actions exclude irreducible degrees eleven and twelve. The existing
degree-ten module equivalence then completes recognition through degree twelve.
The conditional induced-module interface is retained, and the unconditional
theorem below discharges the exact Chapter K recognition obligation.

Source: Aschbacher--Smith K.4, printed p.457/PDF p.468, citing
Guralnick--Malle, Theorem 6.6/Table 6.7; James, J. Algebra 27 (1973), 57--111.
The group marking and the full Representation.Equiv are retained.
-/

public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue.M11Exclusion
universe v

/-- Apply the concrete induced-module degree gap to the exact Chapter K
recognition obligation. -/
theorem smallDegreeRecognition_of_smallInducedHeads
    (hheads : Representation.MathieuSmall.M11DegreeTwelve.SmallInducedHeads) :
    SmallDegreeRecognition.{v} := by
  intro V _ _ _ σ hf hi hd
  let : σ.IsIrreducible := hi
  exact Representation.MathieuSmall.M11DegreeTwelve.equiv_point_of_smallInducedHeads
    σ hheads hf hd

/-- Unconditional recognition of every faithful irreducible binary M11 module
of degree at most twelve, retaining the literal marked module equivalence. -/
theorem smallDegreeRecognition : SmallDegreeRecognition.{v} := by
  intro V _ _ _ σ hf hi hd
  let : σ.IsIrreducible := hi
  exact Representation.MathieuSmall.M11DegreeTwelve.equiv_point_of_faithful_degree_le_twelve
    σ hf hd

end CFSG.Quasithin.ChapterK.SporadicCatalogue.M11Exclusion
