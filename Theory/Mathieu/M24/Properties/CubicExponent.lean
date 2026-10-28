module
public import Theory.Mathieu.M24.Properties.Sylow3
public import Theory.GroupTheory.PGroup.SylowCubeExponent
import all Theory.Mathieu.M24.Properties.Sylow3

/-!
# Exponent three in the actual M₂₄ Sylow subgroup

The existing coordinate multiplication law makes every one of the 27
certified words have cube one. Sylow conjugacy excludes order nine in M₂₄.
The internal import deliberately extends the original Sylow certificate;
its private coordinates do not enter the public statements and no new
permutation enumeration is needed.

Source: the ATLAS M₂₄ generators and Sylow certificate in `Sylow3`;
Aschbacher--Smith 4.3.16, printed p.618.
-/

namespace Sporadic.Mathieu

/-- Every element of the certified Sylow three-subgroup has cube one. -/
public theorem m24Sylow3Subgroup_cube (x : m24Sylow3Subgroup) : x ^ 3 = 1 := by
  obtain ⟨t,ht⟩ := x.property
  apply Subtype.ext
  change x.val ^ 3 = 1
  rw [←ht]
  have hh : product (product t t) t = (0,0,0) :=
    (by decide +kernel : ∀ t : Coordinates, product (product t t) t = (0,0,0)) t
  rw [show 3 = 2+1 from rfl,pow_succ,pow_two,
    ←evaluate_mul,←evaluate_mul,hh,evaluate_one]

/-- Nine divides no element order in the native Witt-design carrier. -/
public theorem m24_not_nine_dvd_orderOf (x : M24) : ¬ 9 ∣ orderOf x :=
  Subgroup.not_nine_dvd_orderOf_of_sylow_cube m24Sylow3 m24Sylow3Subgroup_cube x

end Sporadic.Mathieu
