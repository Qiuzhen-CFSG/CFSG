module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount.Reduction
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount.Relations
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount.Injectivity

/-!
# Counting the specified local kernel of J₄

The normal closure of `(xy)^14` inside the concrete local subgroup has order
2048. Eleven conjugates are commuting involutions, and their binary span is
preserved by the local generators. The checked conjugation tables identify
this span with the normal closure; the first-row certificate distinguishes
all 2048 binary products.

The matrix evaluations, relations and injectivity certificates are proved in
the imported modules. Source for the local subgroup words: ATLAS
`J4G1-max1W1`, as documented in `Cardinality.Subgroup` and `KernelCount.Tables`.
-/

public section
namespace Janko4.Cardinality

/-- The specified normal closure inside the ATLAS local subgroup has order
`2^11`, certified directly in its binary matrix representation. -/
theorem localKernel_card
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    Nat.card (localKernel hA hB) = 2048 :=
  KernelCount.card_of_certificates hA hB
    (KernelCount.basis_square hA hB) (KernelCount.basis_commute hA hB)
    (KernelCount.basis_conj_x hA hB) (KernelCount.basis_conj_y hA hB)
    (KernelCount.representation_basis hA hB) KernelCount.matrixProduct_injective

end Janko4.Cardinality
