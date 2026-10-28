module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount.BinarySpan
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount.Tables

/-!
# Assembly of the concrete local kernel count

The eleven conjugate words lie in the specified normal closure of `(xy)^14`.
If their matrix certificates establish commuting involutions and the two
conjugation tables, their binary span is normal in the local group. Generation
by x and y identifies that span with the specified normal closure. An independent
injectivity certificate on the decoded witness matrices then proves the count
2048. All concrete certificate obligations are explicit hypotheses here.

The words and proposed tables come from the ATLAS local subgroup program;
see `Cardinality.Subgroup` and `KernelCount.Tables` for source attribution.
-/

@[expose] public section
namespace Janko4.Cardinality.KernelCount

variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)

/-- The eleven actual conjugates inside the local subgroup. -/
def basis : Fin 11 → max1Subgroup hA hB :=
  conjugates (localX hA hB) (localY hA hB) (localKernelSeed hA hB)

/-- The faithful matrix representation restricted to the local subgroup. -/
def representation : max1Subgroup hA hB →* BinaryMatrix :=
  toMatrix.comp (max1Subgroup hA hB).subtype

theorem representation_injective : Function.Injective (representation hA hB) :=
  toMatrix_injective.comp Subtype.val_injective

theorem basis_mem_localKernel (i : Fin 11) : basis hA hB i ∈ localKernel hA hB :=
  conjugates_mem _ _ _ _ (localKernelSeed_mem hA hB) i

/-- A product of the decoded candidate matrices, in increasing index order. -/
def matrixProduct (v : Fin 11 → Bool) : BinaryMatrix :=
  binaryProduct (fun i => decodeRows (basisRows i)) v

/-- Evaluation of eleven words suffices to evaluate every binary product. -/
theorem representation_binaryProduct
    (heval : ∀ i, representation hA hB (basis hA hB i) = decodeRows (basisRows i))
    (v : Fin 11 → Bool) :
    representation hA hB (binaryProduct (basis hA hB) v) = matrixProduct v := by
  rw [map_binaryProduct]
  simp only [heval, matrixProduct]

/-- The matrix injectivity obligation transfers to the actual local group. -/
theorem binaryProduct_injective
    (heval : ∀ i, representation hA hB (basis hA hB i) = decodeRows (basisRows i))
    (hinj : Function.Injective matrixProduct) :
    Function.Injective (binaryProduct (basis hA hB)) := by
  intro v w h
  apply hinj
  simpa only [representation_binaryProduct hA hB heval] using
    congrArg (representation hA hB) h

/-- Kernel-count assembly from explicit matrix certificate obligations. -/
theorem card_of_certificates
    (hs : ∀ i, basis hA hB i * basis hA hB i = 1)
    (hc : ∀ i j, Commute (basis hA hB i) (basis hA hB j))
    (hx : ∀ i, (localX hA hB)⁻¹ * basis hA hB i * localX hA hB =
      binaryProduct (basis hA hB) (fun j => (xMasks i).testBit j.val))
    (hy : ∀ i, (localY hA hB)⁻¹ * basis hA hB i * localY hA hB =
      binaryProduct (basis hA hB) (fun j => (yMasks i).testBit j.val))
    (heval : ∀ i, representation hA hB (basis hA hB i) = decodeRows (basisRows i))
    (hinj : Function.Injective matrixProduct) :
    Nat.card (localKernel hA hB) = 2048 := by
  have heq : Subgroup.closure (Set.range (basis hA hB)) = localKernel hA hB := by
    apply closure_conjugates_eq_normalClosure _ _ _ (localXY_generate hA hB)
    · intro i
      change (localX hA hB)⁻¹ * basis hA hB i * localX hA hB ∈ _
      rw [hx]
      exact binaryProduct_mem _ _ _ (fun j =>
        Subgroup.subset_closure (Set.mem_range_self j))
    · intro i
      change (localY hA hB)⁻¹ * basis hA hB i * localY hA hB ∈ _
      rw [hy]
      exact binaryProduct_mem _ _ _ (fun j =>
        Subgroup.subset_closure (Set.mem_range_self j))
  rw [← heq]
  exact card_closure_binaryProduct _ hs hc (binaryProduct_injective hA hB heval hinj)

end Janko4.Cardinality.KernelCount
