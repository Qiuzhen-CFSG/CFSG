module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.FiniteBound.WeightData

/-!
# Two independent certificates for the fixed-mask inequality

For a nontrivial normal elementary subgroup B, choose a nonidentity element
whose assigned weight is least among such elements of B. Every element of B
has at least that weight and commutes with the chosen element. Thus B injects
into the corresponding `Slice`. The normality certificate bounds the common
fixed masks by the chosen weight, and the slice certificate bounds the product.

The slice uses agreement of the two products on just the first three points.
Commutativity implies these equalities; the final argument does not assume the
converse. Both certificates below are proof obligations, not asserted facts.
The actual group and exact row-coordinate action are inherited unchanged from
`FixedCoordinates` through `WeightData` and `Enumeration`.
-/

@[expose] public section
namespace Janko4.LocalStructure.SylowCore.FiniteBoundCertificate
open Simplicity.Max1Fusion.QuotientInvolutions

/-- A computable necessary condition for membership in the chosen commuting slice. -/
def sliceTest (i j : Index) : Prop :=
  weight i ≤ weight j ∧
    ∀ p : Fin 3, perm i (perm j (p.castLE (by decide))) =
      perm j (perm i (p.castLE (by decide)))

instance (i j : Index) : Decidable (sliceTest i j) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A finite overestimate for a subgroup whose least weight occurs at `i`. -/
def Slice (i : Index) := {j : Index // sliceTest i j}

instance (i : Index) : Fintype (Slice i) :=
  inferInstanceAs (Fintype {j : Index // sliceTest i j})

/-- Normality and exponent two must justify every entry in the weight table,
including the zero entries, which exclude the corresponding elements. -/
def NormalFixedCertificate : Prop :=
  ∀ B : Subgroup sylowCandidate, B.Normal → IsElementaryAbelian 2 B →
    ∀ i : Index, element i ∈ B → Nat.card (FixedMasks B) ≤ weight i

/-- A finite count involving only the literal permutations and candidate weights. -/
def SliceCertificate : Prop :=
  ∀ i : Index, i ≠ identityIndex → Nat.card (Slice i) * weight i ≤ 1024

end Janko4.LocalStructure.SylowCore.FiniteBoundCertificate
