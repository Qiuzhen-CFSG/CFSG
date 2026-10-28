module

public import Theory.AlgebraicGroup.Borel.RootStructure

/-!
# Ambient central-series interfaces

This module defines the ambient forms of a closed subgroup's lower central
series, upper central series, and center.  They are the input vocabulary for
GLS3 Theorem 1.12.9 and live below that theorem so its isolated proof target can
be checked using only prior source modules.
-/

set_option warningAsError false

universe u v w

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public def ambientLowerCentralSeries
    {K : Variety k} [AlgebraicGroup K] (U : ClosedSubgroup K) (i : ℕ) :
    Subgroup (Variety.Point K) :=
  U.toSubgroup.lowerCentralSeries i

public def ambientUpperCentralSeries
    {K : Variety k} [AlgebraicGroup K] (U : ClosedSubgroup K) (i : ℕ) :
    Subgroup (Variety.Point K) :=
  Subgroup.map U.toSubgroup.subtype
    (Subgroup.upperCentralSeries U.toSubgroup i)

public def ambientCenter
    {K : Variety k} [AlgebraicGroup K] (U : ClosedSubgroup K) :
    Subgroup (Variety.Point K) :=
  Subgroup.map U.toSubgroup.subtype (Subgroup.center U.toSubgroup)

end Theory.AlgebraicGroup
