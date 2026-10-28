module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.CubicOrbit
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.CubicOrbit.OuterAutomorphisms.Linear
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.CubicOrbit.OuterAutomorphisms.Unitary

/-!
# Discharging the outer-group premise in the cubic-orbit calculation

All three actual surviving carriers have abelian outer automorphism groups.
The linear and unitary model theorems retain their original isomorphisms and
parameter restrictions. This supplies the remaining premise of the source
supplement calculation, without assuming H* = K*X*T*.

Source: Aschbacher–Smith, proof of 13.8.20(a), p.954, combined manuscript
of 1 March 2004; the intrinsic automorphism sources are cited in the imports.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit

/-- Discharge outer commutativity for every actual surviving source carrier. -/
theorem externalCarrier_outer_abelian {D : Type*} [Group D] [IsQuasisimple D]
    (h : Structure.ExternalCarrier D) (hZ : center D = ⊥) :
    IsMulCommutative (MulAut.Outer D) := by
  cases h with
  | linearTwo n hn iso => exact OuterAutomorphisms.linearTwo_outer_isMulCommutative hn iso
  | linearThree n hn ho iso =>
      exact OuterAutomorphisms.linearThree_outer_isMulCommutative hn ho iso
  | unitaryThree n hn he iso =>
      exact OuterAutomorphisms.unitaryThree_outer_isMulCommutative hn he iso hZ

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit
