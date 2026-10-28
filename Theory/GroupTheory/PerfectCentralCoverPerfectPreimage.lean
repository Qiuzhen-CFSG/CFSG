module
public import Theory.GroupTheory.PerfectCentralCoverLocalBound
public import Theory.GroupTheory.SolvableResidual

/-!
# Perfect preimages at index prime to a central kernel

Let E cover G perfectly with central p-group kernel. If P is a perfect
subgroup of G of index prime to p, transfer puts the full kernel into
the embedded solvable residual of its preimage. That residual already
maps onto P, so it is the entire preimage.

The weight-six point stabilizer of A₇ has index seven, prime to the
possible cubic kernel. Its application identifies the original two- and
solvable residuals in Aschbacher--Smith 12.3.6, printed p.809.
-/

public section
open Subgroup
namespace PerfectCentralCovering
variable {E G : Type*} [Group E] [Finite E] [Group G]

/-- Perfectness lifts over a central p-kernel at index prime to p. -/
theorem Cover.perfect_preimage_of_primeToIndex (c : Cover E G)
    {p : ℕ} [Fact p.Prime] (hp : IsPGroup p c.toMonoidHom.ker)
    (P : Subgroup G) [Group.IsPerfect P] (hi : ¬ p ∣ P.index) :
    Group.IsPerfect (P.comap c.toMonoidHom) := by
  let R := P.comap c.toMonoidHom
  let D := (solvableResidual R).map R.subtype
  have hm : D.map c.toMonoidHom = P := by
    rw [show D = (solvableResidual R).map R.subtype from rfl,
      map_solvableResidual_comap c.toMonoidHom c.surjective P,
      solvableResidual_eq_top, ← MonoidHom.range_eq_map, range_subtype]
  have hk : c.toMonoidHom.ker ≤ D :=
    c.central_pSubgroup_le_local_lift D P hm hi _ le_rfl hp
  have hD : D = R := by
    dsimp only [R]
    rw [← hm, comap_map_eq, sup_eq_left.mpr hk]
  let : Group.IsPerfect D := Group.IsPerfect.map R.subtype
  change Group.IsPerfect R
  rw [← hD]
  infer_instance

end PerfectCentralCovering
