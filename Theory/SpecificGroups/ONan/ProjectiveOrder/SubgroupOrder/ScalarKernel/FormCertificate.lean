module

public import Theory.SpecificGroups.ONan.ProjectiveOrder.SubgroupOrder.LinearSetup
public import Theory.SpecificGroups.ONan.ProjectiveOrder.CosetIndex.FixedPlane

/-!
# Invariant form of the O'Nan local lifts

The displayed form is the pullback of an eight-dimensional form along the
ATLAS-derived row basis `fixedPlaneRows`. The existing fixed-plane certificate
identifies the actions of the exact local words on that basis. Entrywise kernel
reduction checks the pullback and the two small isometry identities; matrix
associativity then gives preservation of the ambient form.

The witness is `invariantForm45` produced by `ScalarWitness.g` from the ATLAS
45a matrices (R. A. Wilson, R. A. Parker, J. N. Bray and contributors).
Source matrices and attribution: `refs/original/onan/`; local words:
`ProjectiveOrder/source/README.md`. No group identification is assumed.
-/

namespace ONan.OrderCertificate

set_option maxRecDepth 4096

-- Explicit decisions avoid dependent instance search through the tables.
private def entryDecidable {m n : Nat} (M N : Matrix (Fin m) (Fin n) (ZMod 7)) :
    Decidable (∀ i j, M i j = N i j) :=
  @Nat.decidableForallFin m _ (fun i =>
    @Nat.decidableForallFin n _ (fun j => ZMod.decidableEq 7 (M i j) (N i j)))

/-- The explicit bilinear form preserved by the two lifted local words. -/
@[expose] public def scalarKernelForm : Matrix (Fin 45) (Fin 45) (ZMod 7) :=
  ![![1, 0, 3, 3, 3, 6, 5, 0, 3, 5, 0, 1, 0, 4, 0, 6, 5, 1, 2, 2, 0, 6, 3, 1, 5, 0, 0, 6, 0, 3, 6, 2, 4, 1, 2, 2, 0, 1, 4, 6, 6, 6, 4, 4, 1],
    ![0, 5, 5, 1, 5, 4, 3, 4, 1, 0, 5, 4, 6, 2, 1, 5, 6, 3, 5, 2, 4, 1, 4, 2, 6, 0, 4, 5, 2, 1, 0, 3, 2, 2, 6, 0, 2, 0, 5, 6, 2, 4, 0, 4, 0],
    ![3, 5, 6, 5, 4, 0, 6, 5, 6, 3, 3, 4, 2, 5, 3, 0, 0, 2, 3, 0, 0, 2, 0, 2, 5, 4, 6, 6, 0, 2, 3, 1, 5, 4, 5, 6, 5, 2, 3, 6, 5, 5, 1, 4, 6],
    ![3, 1, 5, 5, 3, 5, 5, 5, 3, 5, 0, 5, 4, 4, 1, 3, 5, 2, 6, 5, 3, 1, 1, 5, 4, 0, 2, 6, 1, 3, 6, 4, 6, 5, 0, 6, 1, 6, 0, 3, 2, 6, 6, 1, 3],
    ![3, 5, 4, 3, 2, 0, 2, 6, 1, 3, 6, 6, 5, 5, 2, 2, 6, 6, 6, 1, 4, 6, 5, 4, 0, 2, 0, 2, 3, 6, 4, 1, 4, 0, 2, 4, 6, 4, 1, 0, 1, 3, 1, 3, 5],
    ![6, 4, 0, 5, 0, 0, 6, 2, 1, 0, 0, 5, 5, 5, 6, 2, 3, 3, 4, 5, 0, 5, 5, 5, 0, 2, 0, 1, 4, 5, 0, 6, 1, 0, 4, 0, 1, 0, 0, 3, 6, 3, 3, 1, 4],
    ![5, 3, 6, 5, 2, 6, 3, 6, 6, 2, 1, 4, 3, 2, 3, 5, 1, 6, 1, 0, 1, 6, 2, 6, 1, 3, 2, 4, 0, 5, 0, 3, 1, 4, 4, 1, 0, 4, 5, 5, 1, 1, 1, 1, 2],
    ![0, 4, 5, 5, 6, 2, 6, 6, 2, 4, 6, 2, 4, 5, 6, 0, 2, 5, 1, 0, 2, 0, 1, 4, 1, 2, 2, 5, 2, 5, 2, 0, 3, 6, 4, 3, 6, 0, 4, 5, 5, 5, 6, 0, 6],
    ![3, 1, 6, 3, 1, 1, 6, 2, 0, 5, 3, 3, 0, 4, 1, 3, 5, 5, 6, 2, 6, 5, 0, 5, 1, 1, 6, 2, 2, 4, 5, 5, 0, 4, 4, 1, 4, 1, 5, 5, 5, 5, 4, 3, 6],
    ![5, 0, 3, 5, 3, 0, 2, 4, 5, 5, 3, 2, 4, 1, 1, 2, 5, 6, 2, 6, 0, 3, 4, 0, 1, 5, 5, 1, 1, 6, 0, 1, 1, 6, 3, 2, 2, 6, 6, 1, 3, 1, 4, 0, 1],
    ![0, 5, 3, 0, 6, 0, 1, 6, 3, 3, 5, 2, 4, 4, 6, 0, 6, 0, 4, 4, 5, 6, 6, 0, 5, 4, 2, 3, 2, 1, 3, 5, 6, 5, 0, 3, 6, 0, 0, 4, 3, 2, 5, 6, 0],
    ![1, 4, 4, 5, 6, 5, 4, 2, 3, 2, 2, 0, 4, 1, 4, 0, 5, 6, 5, 3, 5, 0, 0, 0, 2, 5, 6, 5, 0, 2, 3, 1, 5, 6, 4, 4, 4, 0, 0, 2, 3, 6, 4, 1, 3],
    ![0, 6, 2, 4, 5, 5, 3, 4, 0, 4, 4, 4, 0, 5, 5, 4, 4, 2, 2, 4, 0, 5, 6, 6, 6, 3, 0, 0, 5, 6, 6, 3, 0, 6, 6, 0, 3, 0, 1, 3, 5, 3, 0, 5, 0],
    ![4, 2, 5, 4, 5, 5, 2, 5, 4, 1, 4, 1, 5, 4, 4, 6, 2, 5, 5, 2, 2, 0, 2, 3, 1, 1, 2, 2, 1, 6, 3, 5, 4, 2, 5, 3, 3, 1, 4, 3, 6, 3, 4, 0, 2],
    ![0, 1, 3, 1, 2, 6, 3, 6, 1, 1, 6, 4, 5, 4, 1, 5, 5, 4, 1, 3, 0, 3, 6, 4, 6, 6, 0, 6, 2, 6, 2, 5, 2, 1, 1, 6, 4, 1, 6, 1, 5, 5, 2, 0, 3],
    ![6, 5, 0, 3, 2, 2, 5, 0, 3, 2, 0, 0, 4, 6, 5, 5, 2, 3, 1, 0, 6, 4, 2, 4, 3, 4, 3, 5, 4, 6, 0, 3, 1, 1, 6, 1, 2, 2, 1, 2, 4, 0, 3, 3, 3],
    ![5, 6, 0, 5, 6, 3, 1, 2, 5, 5, 6, 5, 4, 2, 5, 2, 3, 1, 4, 6, 1, 3, 5, 4, 6, 2, 1, 0, 6, 3, 6, 2, 1, 3, 3, 1, 4, 6, 4, 2, 5, 3, 4, 6, 3],
    ![1, 3, 2, 2, 6, 3, 6, 5, 5, 6, 0, 6, 2, 5, 4, 3, 1, 5, 3, 2, 2, 3, 4, 5, 0, 4, 4, 2, 3, 0, 0, 0, 1, 2, 4, 4, 2, 5, 5, 2, 1, 4, 5, 4, 5],
    ![2, 5, 3, 6, 6, 4, 1, 1, 6, 2, 4, 5, 2, 5, 1, 1, 4, 3, 5, 6, 0, 5, 5, 2, 3, 6, 5, 1, 2, 0, 0, 0, 2, 2, 3, 2, 6, 2, 3, 1, 4, 5, 2, 2, 5],
    ![2, 2, 0, 5, 1, 5, 0, 0, 2, 6, 4, 3, 4, 2, 3, 0, 6, 2, 6, 5, 3, 4, 1, 6, 6, 1, 0, 6, 4, 3, 4, 5, 3, 1, 4, 0, 4, 4, 3, 1, 3, 0, 3, 5, 1],
    ![0, 4, 0, 3, 4, 0, 1, 2, 6, 0, 5, 5, 0, 2, 0, 6, 1, 2, 0, 3, 0, 1, 5, 3, 6, 1, 6, 2, 0, 0, 0, 2, 6, 0, 4, 4, 1, 4, 3, 5, 1, 6, 2, 0, 6],
    ![6, 1, 2, 1, 6, 5, 6, 0, 5, 3, 6, 0, 5, 0, 3, 4, 3, 3, 5, 4, 1, 3, 1, 1, 0, 3, 6, 2, 0, 6, 6, 6, 2, 0, 0, 4, 1, 4, 5, 0, 0, 3, 4, 3, 4],
    ![3, 4, 0, 1, 5, 5, 2, 1, 0, 4, 6, 0, 6, 2, 6, 2, 5, 4, 5, 1, 5, 1, 0, 2, 5, 3, 5, 5, 4, 3, 6, 5, 1, 6, 1, 2, 3, 1, 5, 0, 3, 2, 2, 3, 0],
    ![1, 2, 2, 5, 4, 5, 6, 4, 5, 0, 0, 0, 6, 3, 4, 4, 4, 5, 2, 6, 3, 1, 2, 4, 4, 5, 4, 5, 4, 5, 3, 2, 3, 5, 6, 6, 1, 6, 3, 0, 2, 4, 0, 1, 3],
    ![5, 6, 5, 4, 0, 0, 1, 1, 1, 1, 5, 2, 6, 1, 6, 3, 6, 0, 3, 6, 6, 0, 5, 4, 0, 6, 6, 5, 2, 6, 5, 2, 2, 3, 1, 0, 3, 1, 5, 1, 0, 3, 3, 3, 3],
    ![0, 0, 4, 0, 2, 2, 3, 2, 1, 5, 4, 5, 3, 1, 6, 4, 2, 4, 6, 1, 1, 3, 3, 5, 6, 0, 6, 2, 1, 2, 3, 5, 1, 1, 4, 2, 5, 4, 6, 1, 6, 0, 2, 0, 0],
    ![0, 4, 6, 2, 0, 0, 2, 2, 6, 5, 2, 6, 0, 2, 0, 3, 1, 4, 5, 0, 6, 6, 5, 4, 6, 6, 5, 2, 1, 5, 5, 0, 3, 0, 5, 0, 4, 1, 6, 4, 2, 1, 5, 5, 4],
    ![6, 5, 6, 6, 2, 1, 4, 5, 2, 1, 3, 5, 0, 2, 6, 5, 0, 2, 1, 6, 2, 2, 5, 5, 5, 2, 2, 5, 6, 2, 0, 0, 0, 6, 2, 4, 3, 5, 3, 0, 6, 6, 3, 6, 4],
    ![0, 2, 0, 1, 3, 4, 0, 2, 2, 1, 2, 0, 5, 1, 2, 4, 6, 3, 2, 4, 0, 0, 4, 4, 2, 1, 1, 6, 3, 6, 0, 1, 2, 2, 0, 6, 1, 1, 6, 6, 5, 0, 5, 1, 3],
    ![3, 1, 2, 3, 6, 5, 5, 5, 4, 6, 1, 2, 6, 6, 6, 6, 3, 0, 0, 3, 0, 6, 3, 5, 6, 2, 5, 2, 6, 4, 4, 5, 6, 0, 1, 4, 6, 2, 4, 1, 3, 0, 1, 5, 2],
    ![6, 0, 3, 6, 4, 0, 0, 2, 5, 0, 3, 3, 6, 3, 2, 0, 6, 0, 0, 4, 0, 6, 6, 3, 5, 3, 5, 0, 0, 4, 6, 3, 6, 5, 5, 2, 1, 5, 0, 2, 4, 1, 0, 1, 4],
    ![2, 3, 1, 4, 1, 6, 3, 0, 5, 1, 5, 1, 3, 5, 5, 3, 2, 0, 0, 5, 2, 6, 5, 2, 2, 5, 0, 0, 1, 5, 3, 3, 5, 2, 1, 0, 5, 1, 3, 2, 3, 0, 3, 2, 0],
    ![4, 2, 5, 6, 4, 1, 1, 3, 0, 1, 6, 5, 0, 4, 2, 1, 1, 1, 2, 3, 6, 2, 1, 3, 2, 1, 3, 0, 2, 6, 6, 5, 3, 1, 5, 4, 4, 3, 3, 2, 0, 5, 6, 4, 1],
    ![1, 2, 4, 5, 0, 0, 4, 6, 4, 6, 5, 6, 6, 2, 1, 1, 3, 2, 2, 1, 0, 0, 6, 5, 3, 1, 0, 6, 2, 0, 5, 2, 1, 3, 6, 2, 4, 5, 5, 3, 1, 4, 3, 5, 1],
    ![2, 6, 5, 0, 2, 4, 4, 4, 4, 3, 0, 4, 6, 5, 1, 6, 3, 4, 3, 4, 4, 0, 1, 6, 1, 4, 5, 2, 0, 1, 5, 1, 5, 6, 1, 0, 0, 2, 4, 2, 2, 2, 5, 2, 1],
    ![2, 0, 6, 6, 4, 0, 1, 3, 1, 2, 3, 4, 0, 3, 6, 1, 1, 4, 2, 0, 4, 4, 2, 6, 0, 2, 0, 4, 6, 4, 2, 0, 4, 2, 0, 4, 1, 6, 4, 1, 4, 3, 0, 6, 0],
    ![0, 2, 5, 1, 6, 1, 0, 6, 4, 2, 6, 4, 3, 3, 4, 2, 4, 2, 6, 4, 1, 1, 3, 1, 3, 5, 4, 3, 1, 6, 1, 5, 4, 4, 0, 1, 0, 5, 1, 6, 0, 5, 5, 5, 6],
    ![1, 0, 2, 6, 4, 0, 4, 0, 1, 6, 0, 0, 0, 1, 1, 2, 6, 5, 2, 4, 4, 4, 1, 6, 1, 4, 1, 5, 1, 2, 5, 1, 3, 5, 2, 6, 5, 0, 2, 1, 0, 5, 5, 5, 2],
    ![4, 5, 3, 0, 1, 0, 5, 4, 5, 6, 0, 0, 1, 4, 6, 1, 4, 5, 3, 3, 3, 5, 5, 3, 5, 6, 6, 3, 6, 4, 0, 3, 3, 5, 4, 4, 1, 2, 0, 4, 5, 1, 1, 1, 5],
    ![6, 6, 6, 3, 0, 3, 5, 5, 5, 1, 4, 2, 3, 3, 1, 2, 2, 2, 1, 1, 5, 0, 0, 0, 1, 1, 4, 0, 6, 1, 2, 2, 2, 3, 2, 1, 6, 1, 4, 5, 0, 0, 3, 2, 0],
    ![6, 2, 5, 2, 1, 6, 1, 5, 5, 3, 3, 3, 5, 6, 5, 4, 5, 1, 4, 3, 1, 0, 3, 2, 0, 6, 2, 6, 5, 3, 4, 3, 0, 1, 2, 4, 0, 0, 5, 0, 4, 0, 3, 5, 3],
    ![6, 4, 5, 6, 3, 3, 1, 5, 5, 1, 2, 6, 3, 3, 5, 0, 3, 4, 5, 0, 6, 3, 2, 4, 3, 0, 1, 6, 0, 0, 1, 0, 5, 4, 2, 3, 5, 5, 1, 0, 0, 1, 6, 2, 6],
    ![4, 0, 1, 6, 1, 3, 1, 6, 4, 4, 5, 4, 0, 4, 2, 3, 4, 5, 2, 3, 2, 4, 2, 0, 3, 2, 5, 3, 5, 1, 0, 3, 6, 3, 5, 0, 5, 5, 1, 3, 3, 6, 5, 5, 3],
    ![4, 4, 4, 1, 3, 1, 1, 0, 3, 0, 6, 1, 5, 0, 0, 3, 6, 4, 2, 5, 0, 3, 3, 1, 3, 0, 5, 6, 1, 5, 1, 2, 4, 5, 2, 6, 5, 5, 1, 2, 5, 2, 5, 4, 0],
    ![1, 0, 6, 3, 5, 4, 2, 6, 6, 1, 0, 3, 0, 2, 3, 3, 3, 5, 5, 1, 6, 4, 0, 3, 3, 0, 4, 4, 3, 2, 4, 0, 1, 1, 1, 0, 6, 2, 5, 0, 3, 6, 3, 0, 1]]

private def smallForm : Matrix (Fin 8) (Fin 8) (ZMod 7) :=
  ![![1, 0, 3, 3, 3, 6, 5, 0],
    ![0, 5, 5, 1, 5, 4, 3, 4],
    ![3, 5, 6, 5, 4, 0, 6, 5],
    ![3, 1, 5, 5, 3, 5, 5, 5],
    ![3, 5, 4, 3, 2, 0, 2, 6],
    ![6, 4, 0, 5, 0, 0, 6, 2],
    ![5, 3, 6, 5, 2, 6, 3, 6],
    ![0, 4, 5, 5, 6, 2, 6, 6]]

private def pullbackLeft : Matrix (Fin 45) (Fin 8) (ZMod 7) :=
  ![![1, 0, 3, 3, 3, 6, 5, 0],
    ![0, 5, 5, 1, 5, 4, 3, 4],
    ![3, 5, 6, 5, 4, 0, 6, 5],
    ![3, 1, 5, 5, 3, 5, 5, 5],
    ![3, 5, 4, 3, 2, 0, 2, 6],
    ![6, 4, 0, 5, 0, 0, 6, 2],
    ![5, 3, 6, 5, 2, 6, 3, 6],
    ![0, 4, 5, 5, 6, 2, 6, 6],
    ![3, 1, 6, 3, 1, 1, 6, 2],
    ![5, 0, 3, 5, 3, 0, 2, 4],
    ![0, 5, 3, 0, 6, 0, 1, 6],
    ![1, 4, 4, 5, 6, 5, 4, 2],
    ![0, 6, 2, 4, 5, 5, 3, 4],
    ![4, 2, 5, 4, 5, 5, 2, 5],
    ![0, 1, 3, 1, 2, 6, 3, 6],
    ![6, 5, 0, 3, 2, 2, 5, 0],
    ![5, 6, 0, 5, 6, 3, 1, 2],
    ![1, 3, 2, 2, 6, 3, 6, 5],
    ![2, 5, 3, 6, 6, 4, 1, 1],
    ![2, 2, 0, 5, 1, 5, 0, 0],
    ![0, 4, 0, 3, 4, 0, 1, 2],
    ![6, 1, 2, 1, 6, 5, 6, 0],
    ![3, 4, 0, 1, 5, 5, 2, 1],
    ![1, 2, 2, 5, 4, 5, 6, 4],
    ![5, 6, 5, 4, 0, 0, 1, 1],
    ![0, 0, 4, 0, 2, 2, 3, 2],
    ![0, 4, 6, 2, 0, 0, 2, 2],
    ![6, 5, 6, 6, 2, 1, 4, 5],
    ![0, 2, 0, 1, 3, 4, 0, 2],
    ![3, 1, 2, 3, 6, 5, 5, 5],
    ![6, 0, 3, 6, 4, 0, 0, 2],
    ![2, 3, 1, 4, 1, 6, 3, 0],
    ![4, 2, 5, 6, 4, 1, 1, 3],
    ![1, 2, 4, 5, 0, 0, 4, 6],
    ![2, 6, 5, 0, 2, 4, 4, 4],
    ![2, 0, 6, 6, 4, 0, 1, 3],
    ![0, 2, 5, 1, 6, 1, 0, 6],
    ![1, 0, 2, 6, 4, 0, 4, 0],
    ![4, 5, 3, 0, 1, 0, 5, 4],
    ![6, 6, 6, 3, 0, 3, 5, 5],
    ![6, 2, 5, 2, 1, 6, 1, 5],
    ![6, 4, 5, 6, 3, 3, 1, 5],
    ![4, 0, 1, 6, 1, 3, 1, 6],
    ![4, 4, 4, 1, 3, 1, 1, 0],
    ![1, 0, 6, 3, 5, 4, 2, 6]]

/-- A unit entry makes the scalar constraint nontrivial. -/
public theorem scalarKernelForm_zero_zero : scalarKernelForm 0 0 = 1 := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem pullback_left : fixedPlaneRows.transpose * smallForm = pullbackLeft := by
  apply Matrix.ext
  exact @of_decide_eq_true _ (entryDecidable _ _) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem pullback_right : pullbackLeft * fixedPlaneRows = scalarKernelForm := by
  apply Matrix.ext
  exact @of_decide_eq_true _ (entryDecidable _ _) (by decide +kernel)

private theorem form_eq_pullback :
    scalarKernelForm = fixedPlaneRows.transpose * smallForm * fixedPlaneRows := by
  rw [pullback_left, pullback_right]

set_option maxHeartbeats 0 in
private theorem smallForm_A :
    fixedPlaneActionA.transpose * smallForm * fixedPlaneActionA = smallForm := by
  apply Matrix.ext
  exact @of_decide_eq_true _ (entryDecidable _ _) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem smallForm_B :
    fixedPlaneActionB.transpose * smallForm * fixedPlaneActionB = smallForm := by
  apply Matrix.ext
  exact @of_decide_eq_true _ (entryDecidable _ _) (by decide +kernel)

private theorem preserves_pullback
    (M : Matrix (Fin 45) (Fin 45) (ZMod 7))
    (a : Matrix (Fin 8) (Fin 8) (ZMod 7))
    (ha : fixedPlaneRows * M = a * fixedPlaneRows)
    (hform : a.transpose * smallForm * a = smallForm) :
    M.transpose * scalarKernelForm * M = scalarKernelForm := by
  rw [form_eq_pullback]
  calc
    _ = (fixedPlaneRows * M).transpose * smallForm * (fixedPlaneRows * M) := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = (a * fixedPlaneRows).transpose * smallForm * (a * fixedPlaneRows) := by rw [ha]
    _ = fixedPlaneRows.transpose * (a.transpose * smallForm * a) * fixedPlaneRows := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = fixedPlaneRows.transpose * smallForm * fixedPlaneRows := by rw [hform]

/-- The first exact local lift preserves the displayed form. -/
public theorem linearLocalA_preserves_scalarKernelForm :
    linearLocalA.val.transpose * scalarKernelForm * linearLocalA.val = scalarKernelForm :=
  preserves_pullback linearLocalA.val fixedPlaneActionA fixedPlaneRows_localA smallForm_A

/-- The second exact local lift preserves the displayed form. -/
public theorem linearLocalB_preserves_scalarKernelForm :
    linearLocalB.val.transpose * scalarKernelForm * linearLocalB.val = scalarKernelForm :=
  preserves_pullback linearLocalB.val fixedPlaneActionB fixedPlaneRows_localB smallForm_B

end ONan.OrderCertificate
