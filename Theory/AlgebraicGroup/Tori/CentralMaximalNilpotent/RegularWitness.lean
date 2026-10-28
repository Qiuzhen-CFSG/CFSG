module

public import Theory.AlgebraicGroup.Tori.CentralMaximalNilpotent
public import Theory.AlgebraicGroup.Borel.ElementCoverage.RegularWitness.Cartan

/-!
# Applying the central-torus quotient to regular fixed cosets

Borel §11.5 supplies nilpotence of the literal Cartan component through
`CentralMaximalNilpotent`. This module substitutes that nilpotence into
the existing `regularFixedCosetData_of_nilpotent_of_regular` constructor. The
remaining regular-point input is exactly §8.18. The conditional torus-free
interface is retained; the terminal constructor discharges its unipotence
premise. Final regular-point assembly remains with the Cartan witness consumer.

Source: `refs/KGroup/Bor1/Chapter4.tex`, §§11.5, 11.7, 11.10, and
`refs/KGroup/Bor1/Chapter3.tex`, §8.18.
-/

namespace Theory.AlgebraicGroup.BorelElementCoverage

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

/-- Discharge the nilpotence argument of the actual regular fixed-coset
constructor by the central maximal torus quotient. The earlier source
unipotence assertion and the regular element remain explicit. -/
public noncomputable def regularFixedCosetData_of_torusFree_unipotence_of_regular
    (hunip : ∀ (K : Variety k) [AlgebraicGroup K], Variety.IsConnected K →
      (∀ R : ClosedSubgroup K, IsSubtorus R → R.toSubgroup = ⊥) →
      IsUnipotentAlgebraicGroup K)
    {T : ClosedSubgroup G} (hT : IsMaximalTorus T)
    (t : Variety.Point G) (htT : t ∈ T.toSubgroup)
    (hregular : (semisimpleCommutatorPointCentralizer t).identityComponentAmbient =
      T.centralizer.identityComponentAmbient) :
    RegularFixedCosetData T.centralizer.identityComponentAmbient :=
  regularFixedCosetData_of_nilpotent_of_regular hT
    (CentralMaximalNilpotent.centralizerComponent_isNilpotent_of_torusFree_unipotence
      hunip hT) t htT hregular

/-- Apply Borel §11.7 to discharge `hnil` in the actual regular fixed-coset
constructor. Only the maximal torus and its §8.18 regular point are required. -/
public noncomputable def regularFixedCosetData_of_regular
    {T : ClosedSubgroup G} (hT : IsMaximalTorus T)
    (t : Variety.Point G) (htT : t ∈ T.toSubgroup)
    (hregular : (semisimpleCommutatorPointCentralizer t).identityComponentAmbient =
      T.centralizer.identityComponentAmbient) :
    RegularFixedCosetData T.centralizer.identityComponentAmbient :=
  regularFixedCosetData_of_nilpotent_of_regular hT
    (CentralMaximalNilpotent.centralizerComponent_isNilpotent hT) t htT hregular

end Theory.AlgebraicGroup.BorelElementCoverage
