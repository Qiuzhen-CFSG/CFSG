module

public import Theory.SpecificGroups.Thompson.Model.Order.Cosets.Bounds

/-!
# Index assembly for the concrete Thompson word subgroup

A cover of size 143127000 and an independent family of that many distinct
cosets certify the proposed index. Alternatively, the lower bound can come
from an actual orbit whose base point is fixed by both subgroup generators.
The cover and lower-bound certificates still need construction; these
conditional implications assert neither of them.

The candidate index and the precise subgroup words come from
https://brauer.maths.qmul.ac.uk/Atlas/v3/subgroup/ThG1-max1W1 .
The elementary counting bounds are proved in `Cosets.Bounds` without knowing
the order of the ambient group or subgroup.
-/

namespace Thompson.OrderCertificate

/-- Independent upper and lower certificates give the proposed exact index.
This conditional statement does not assert that either certificate exists. -/
public theorem localSubgroup_index_of_coset_certificates
    (C : Subgroup.GeneratorCosetCover localSubgroup cosetGenerators (Fin 143127000))
    (repr : Fin 143127000 → Model)
    (separate : ∀ i j, repr i * (repr j)⁻¹ ∈ localSubgroup → i = j) :
    localSubgroup.index = 143127000 := by
  apply Nat.le_antisymm
  · simpa only [Nat.card_fin] using localSubgroup_index_le_of_cover C
  · simpa only [Nat.card_fin] using localSubgroup_index_ge_of_separated repr separate

/-- A cover and a sufficiently large actual orbit also certify the index.
The orbit lower bound plus the cover removes the need to assume stabilizer
equality; fixing the two specified words is still required. -/
public theorem localSubgroup_index_of_cover_and_orbit
    (C : Subgroup.GeneratorCosetCover localSubgroup cosetGenerators (Fin 143127000))
    {X : Type*} [MulAction Model X] (x : X)
    (ha : localA • x = x) (hb : localB • x = x)
    (hcard : 143127000 ≤ (MulAction.orbit Model x).ncard) :
    localSubgroup.index = 143127000 := by
  apply Nat.le_antisymm
  · simpa only [Nat.card_fin] using localSubgroup_index_le_of_cover C
  · exact hcard.trans (localSubgroup_orbit_card_le_index x ha hb)

end Thompson.OrderCertificate
