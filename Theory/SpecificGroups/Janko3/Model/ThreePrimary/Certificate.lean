module

public import Theory.SpecificGroups.Janko3.Model.ThreePrimary.Collection

/-!
# Separation of the J₃ Sylow-three normal forms

The checked left inverse on one permutation letter makes the 243 collected
normal forms distinct. The expensive closed permutation checks are compiled
separately in `Collection`, so proof elaboration here does not repeat them.
Source: the actual ATLAS J3G1-p6156B0 permutations; GLS III, Table 5.3h.
-/

namespace Sporadic.Janko3.ThreePrimary

public theorem representative_injective :
    Function.Injective (fun r : Fin 243 => representative 5 r.val) := by
  intro a b hab
  change representative 5 a.val = representative 5 b.val at hab
  rw [← representative_point_inverse a, ← representative_point_inverse b, hab]

end Sporadic.Janko3.ThreePrimary
