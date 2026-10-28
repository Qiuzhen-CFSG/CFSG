module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.Data
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount.Relations

/-!
# Transferring a presentation bound to the actual local quotient

Evaluation sends the two abstract generators to the concrete ATLAS local
matrices. If every relator evaluates into the specified normal closure, this
map descends to a surjection onto `H/N`. A finite upper bound on the presented
group therefore bounds the actual quotient. The matrix-certificate version
uses the already checked eleven kernel words to certify relator membership.

The relators and their source convention are documented in `UpperBound.Data`.
Neither an order for the presentation nor its matrix relator evaluations is
assumed silently: both remain explicit premises of the assembly theorem.
-/

@[expose] public section
namespace Janko4.Cardinality.QuotientCount.UpperBound
open KernelCount

variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)

/-- The ordered pair of concrete local generators. -/
def localGenerators : Bool → max1Subgroup hA hB
  | false => localX hA hB
  | true => localY hA hB

/-- Evaluate an abstract relator in the actual matrix subgroup, before quotienting. -/
def localRelator (i : Fin 47) : max1Subgroup hA hB :=
  FreeGroup.lift (localGenerators hA hB) (relatorWord i)

/-- The quotient images of the same ordered pair. -/
def quotientGenerators (b : Bool) : LocalQuotient hA hB :=
  QuotientGroup.mk' (localKernel hA hB) (localGenerators hA hB b)

theorem localGenerators_generate :
    Subgroup.closure (Set.range (localGenerators hA hB)) = ⊤ := by
  have hr : Set.range (localGenerators hA hB) = {localX hA hB, localY hA hB} := by
    ext g
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨b, rfl⟩
      cases b <;> simp [localGenerators]
    · rintro (rfl | rfl)
      · exact ⟨false, rfl⟩
      · exact ⟨true, rfl⟩
  rw [hr, localXY_generate]

theorem quotientGenerators_generate :
    Subgroup.closure (Set.range (quotientGenerators hA hB)) = ⊤ := by
  have hr : Set.range (quotientGenerators hA hB) =
      (QuotientGroup.mk' (localKernel hA hB)) '' Set.range (localGenerators hA hB) :=
    (Set.range_comp _ _).trans rfl
  rw [hr, ← MonoidHom.map_closure, localGenerators_generate]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

/-- Relator membership is exactly the relation required by the universal property. -/
theorem quotient_relator_eq_one
    (hrel : ∀ i, localRelator hA hB i ∈ localKernel hA hB)
    (r : FreeGroup Bool) (hr : r ∈ Set.range relatorWord) :
    FreeGroup.lift (quotientGenerators hA hB) r = 1 := by
  obtain ⟨i, rfl⟩ := hr
  have he := FreeGroup.lift_unique
    ((QuotientGroup.mk' (localKernel hA hB)).comp
      (FreeGroup.lift (localGenerators hA hB)))
    (f := quotientGenerators hA hB) (by intro b; simp [quotientGenerators])
    (x := relatorWord i)
  rw [← he]
  exact (QuotientGroup.eq_one_iff _).mpr (hrel i)

/-- The homomorphism from the candidate presentation to the actual quotient. -/
def presentationToQuotient
    (hrel : ∀ i, localRelator hA hB i ∈ localKernel hA hB) :
    Presentation →* LocalQuotient hA hB :=
  PresentedGroup.toGroup (quotient_relator_eq_one hA hB hrel)

@[simp] theorem presentationToQuotient_of
    (hrel : ∀ i, localRelator hA hB i ∈ localKernel hA hB) (b : Bool) :
    presentationToQuotient hA hB hrel (PresentedGroup.of b) =
      quotientGenerators hA hB b := PresentedGroup.toGroup.of _

theorem presentationToQuotient_surjective
    (hrel : ∀ i, localRelator hA hB i ∈ localKernel hA hB) :
    Function.Surjective (presentationToQuotient hA hB hrel) := by
  rw [← MonoidHom.range_eq_top, ← top_le_iff,
    ← quotientGenerators_generate hA hB, Subgroup.closure_le]
  rintro _ ⟨b, rfl⟩
  exact ⟨PresentedGroup.of b, presentationToQuotient_of hA hB hrel b⟩

/-- Matrix equality to a certified binary product implies membership in `N`. -/
theorem relator_mem_of_matrix_evaluation (i : Fin 47)
    (heval : representation hA hB (localRelator hA hB i) =
      matrixProduct (fun j => (relatorMask i).testBit j.val)) :
    localRelator hA hB i ∈ localKernel hA hB := by
  have he : localRelator hA hB i =
      binaryProduct (basis hA hB) (fun j => (relatorMask i).testBit j.val) := by
    apply representation_injective hA hB
    rw [representation_binaryProduct hA hB (representation_basis hA hB)]
    exact heval
  rw [he]
  exact binaryProduct_mem _ _ _ (basis_mem_localKernel hA hB)

/-- A finite presentation bound and certified relator membership bound `H/N`.
Finiteness is essential because `Nat.card` of an infinite type is zero. -/
theorem card_le_of_relators
    (hrel : ∀ i, localRelator hA hB i ∈ localKernel hA hB)
    (hbound : Finite Presentation ∧ Nat.card Presentation ≤ 244823040) :
    Nat.card (LocalQuotient hA hB) ≤ 244823040 := by
  let := hbound.1
  exact (Nat.card_le_card_of_surjective _
    (presentationToQuotient_surjective hA hB hrel)).trans hbound.2

/-- Assembly from the two independent concrete certificate obligations. -/
theorem card_le_of_matrix_certificates
    (heval : ∀ i, representation hA hB (localRelator hA hB i) =
      matrixProduct (fun j => (relatorMask i).testBit j.val))
    (hbound : Finite Presentation ∧ Nat.card Presentation ≤ 244823040) :
    Nat.card (LocalQuotient hA hB) ≤ 244823040 :=
  card_le_of_relators hA hB
    (fun i => relator_mem_of_matrix_evaluation hA hB i (heval i)) hbound

end Janko4.Cardinality.QuotientCount.UpperBound
