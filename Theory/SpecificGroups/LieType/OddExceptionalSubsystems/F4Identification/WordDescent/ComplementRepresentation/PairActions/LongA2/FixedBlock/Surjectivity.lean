module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions.LongA2.FixedBlock
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions.LongA2.FixedBlock.Surjectivity.RootFibres

/-!
# The comparison covers the fixed E6 diagram space

Every full projection fibre is a diagram orbit. A fixed vector can therefore be
recovered from one lift of each F4 root and one Cartan representative of each
node fibre. This proves surjectivity of the existing comparison under the
explicit root-image containment premise, over any field, including
characteristic three. Transporting the actual F4 matrix-cover action gives its
marked fixed-space representation once the integral curve identity is supplied.

The parent `LongA2` assembly discharges image containment using
`qt-a02-f4-projection-root-fibres` and the displayed polynomial identity using
`qt-a02-f4-folded-adjoint-integral-curves`; neither is assumed as an instance.
The complementary intertwining remains with its independent owner.

Sources: GLS3 §2.6.2 and the F4 inclusions of Aschbacher--Smith A.2.17,
printed p.39 of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.LongA2.FixedBlock
open WordDescent AdjointRestriction Matrix
attribute [local instance] Classical.decEq
local instance : Fintype typeF4Roots := Fintype.ofFinite _
variable (F : Type*) [Field F]

/-- Reconstruct a fixed vector by reading one Cartan representative and one
root lift in each projection fibre. This works in every characteristic. -/
theorem comparison_surjective_of_root_image
    (himage : ∀ r : typeE6Roots, rootProjection r.val ∈ typeF4Roots) :
    Function.Surjective (comparison F) := by
  intro v
  have hv (i : TwistedE6.Index) :
      v.val (typeE6PinnedIndexEquiv i) = v.val i :=
    congrFun (show diagramLinear F v.val = v.val by
      simpa only [mem_eigenspace, one_smul] using v.property) i
  let representative : Fin 4 → Fin 6 := ![3, 2, 1, 0]
  let lift : typeF4Roots → typeE6Roots := fun s => (root_lifts s).choose
  have hlift (s : typeF4Roots) : rootProjection (lift s).val = s.val :=
    (root_lifts s).choose_spec
  let x : SourceIndex → F
    | .inl j => v.val (.inl (simpleIndex
        (representative (typeF4RootPairing_baseEquiv.symm j))))
    | .inr s => v.val (.inr (lift s))
  refine ⟨x, Subtype.ext ?_⟩
  funext k
  change AdjointRestriction.linearMap F x k = v.val k
  rcases k with j | r
  · obtain ⟨i, rfl⟩ := typeE6RootPairing_baseEquiv.surjective j
    rw [linearMap_cartan]
    simp only [x, sourceIndex, Equiv.symm_apply_apply]
    change v.val (.inl (simpleIndex (representative (node i)))) =
      v.val (.inl (simpleIndex i))
    have hc (i : Fin 6) :
        v.val (.inl (simpleIndex (typeE6DiagramPermutation i))) =
          v.val (.inl (simpleIndex i)) := by
      simpa only [typeE6PinnedIndexEquiv_inl, simpleIndex,
        typeE6DiagramBasePermutation_numbered] using hv (.inl (simpleIndex i))
    fin_cases i
    · rfl
    · rfl
    · rfl
    · rfl
    · exact hc 4
    · exact hc 5
  · let s : typeF4Roots := ⟨rootProjection r.val, himage r⟩
    rw [linearMap_root F x r s rfl]
    change v.val (.inr (lift s)) = v.val (.inr r)
    rcases rootProjection_fibre r (lift s) (hlift s).symm with h | h
    · rw [h]
    · rw [h]
      exact hv (.inr r)

/-- The actual F4 matrix-cover representation on the full fixed diagram space,
using the proved surjectivity of the literal comparison map. -/
def representationOfRootImage
    (himage : ∀ r : typeE6Roots, rootProjection r.val ∈ typeF4Roots) :
    Cover F →* (fixedSpace F ≃ₗ[F] fixedSpace F) :=
  representation F (comparison_surjective_of_root_image F himage)

@[simp] theorem representationOfRootImage_comparison
    (himage : ∀ r : typeE6Roots, rootProjection r.val ∈ typeF4Roots)
    (g : Cover F) (x : SourceIndex → F) :
    representationOfRootImage F himage g (comparison F x) =
      comparison F (g.val.val *ᵥ x) :=
  representation_comparison F (comparison_surjective_of_root_image F himage) g x

/-- The independent integral polynomial comparison marks both signs with the
original parameter. No division by three or irreducibility is required. -/
theorem representationOfRootImage_simple
    (himage : ∀ r : typeE6Roots, rootProjection r.val ∈ typeF4Roots)
    (hpoly : ∀ s i,
      foldedCurve (Polynomial ℤ) s i Polynomial.X * matrix (Polynomial ℤ) =
        matrix (Polynomial ℤ) * sourceCurve (Polynomial ℤ) s i Polynomial.X)
    (s : Bool) (i : Fin 4) (t : F) :
    representationOfRootImage F himage (coverSimple F s i t) =
      eigenspaceAction F 1 (f4Simple F s i t) :=
  representation_simple F (comparison_surjective_of_root_image F himage) hpoly s i t

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.LongA2.FixedBlock
