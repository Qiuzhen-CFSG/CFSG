module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.ExteriorVanishing.Reduction
public import Theory.Representation.SL5TenDimensionalFirstCohomology.ExteriorVanishing.SquareRelations
public import Theory.Representation.SL5TenDimensionalFirstCohomology.ExteriorVanishing.CubeRelations
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Models
public import Theory.Representation.FirstCohomology

/-!
# Exterior-power first cohomology of SL₅(2)

Every crossed homomorphism on the second or third exterior power of the natural
SL₅(2) module is principal, so both first cohomology spaces vanish. The
elementary-generator reduction expresses this as exactness of two finite binary
linear systems, proved by the square and cube relation calculations.

Reference: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma I.1.6(7), printed p.408/PDF p.419, citing Jones--Parshall [JP76].
-/

public section

namespace Representation.SL5TenDimensional
open OneCohomology

/-- Every crossed homomorphism on the exterior square of the natural SL₅(2)
module is principal. -/
theorem exteriorSquare_cocycles_principal (f : cocycles (exteriorAction 2)) :
    ∃ v, principal (exteriorAction 2) v = f :=
  cocycles_principal_of_elementaryRelations 2 elementaryRelations_exact_two f

/-- Every crossed homomorphism on the exterior cube of the natural SL₅(2)
module is principal. -/
theorem exteriorCube_cocycles_principal (f : cocycles (exteriorAction 3)) :
    ∃ v, principal (exteriorAction 3) v = f :=
  cocycles_principal_of_elementaryRelations 3 elementaryRelations_exact_three f

/-- The first cohomology of the exterior square of the natural SL₅(2) module
vanishes (Aschbacher--Smith I.1.6(7)). -/
theorem exteriorSquare_h1_subsingleton : Subsingleton (H1 (exteriorAction 2)) :=
  h1_subsingleton_of_elementaryRelations 2 elementaryRelations_exact_two

/-- The first cohomology of the exterior cube of the natural SL₅(2) module
vanishes (Aschbacher--Smith I.1.6(7)). -/
theorem exteriorCube_h1_subsingleton : Subsingleton (H1 (exteriorAction 3)) :=
  h1_subsingleton_of_elementaryRelations 3 elementaryRelations_exact_three

end Representation.SL5TenDimensional
