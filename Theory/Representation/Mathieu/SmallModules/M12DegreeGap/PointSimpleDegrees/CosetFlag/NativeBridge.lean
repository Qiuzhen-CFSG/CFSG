module

public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees.CosetFlag.Construction

/-!
# From a checked native action table to the actual coset coordinates

The indexed cosets are literally the left cosets of the published A/B words.
Closure of their range under A and B proves surjectivity, since these generate
M₁₁ as a monoid. Both types have cardinality 720, so surjectivity gives a
bijection. Evaluation at this bijection identifies the inverse-permutation
action on functions with the forward-action column matrices.

Consequently the finite producer only needs to certify the two native action
tables. Pairwise distinctness of 720 cosets need not be checked separately.
Source: James, J. Algebra 27 (1973), 57–111; `../source/README.md`.
-/

@[expose] public section
open Sporadic.Mathieu
namespace Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.CosetFlag.NativeBridge

noncomputable def representative (j : Fin 720) : M11 :=
  ((Witness.wordData[j.val]!).map generator).prod

noncomputable def cosetAt (j : Fin 720) : ElevenCoset :=
  QuotientGroup.mk (representative j)

def leftIndex (s : Fin 2) (j : Fin 720) : Fin 720 :=
  (Witness.leftAction[s.val]!)[j.val]!

/-- A finite equality assertion on the literal native cosets. -/
def NativeAction : Prop :=
  ∀ (s : Fin 2) (j : Fin 720), cosetAt (leftIndex s j) = generator s • cosetAt j

theorem cosetAt_zero : cosetAt 0 = QuotientGroup.mk (1 : M11) := by
  have hw : Witness.wordData[0]! = [] := by decide +kernel
  simp only [cosetAt, representative, Fin.val_zero, hw, List.map_nil, List.prod_nil]

theorem cosetAt_surjective (h : NativeAction) : Function.Surjective cosetAt := by
  have horbit (g : M11) : ∃ j, cosetAt j = QuotientGroup.mk g := by
    apply Submonoid.induction_of_closure_eq_top_left
      (motive := fun g => ∃ j, cosetAt j = QuotientGroup.mk g)
      Construction.generators_monoid_closure g
    · exact ⟨0, cosetAt_zero⟩
    · rintro _ ⟨s, rfl⟩ g ⟨j, hj⟩
      refine ⟨leftIndex s j, ?_⟩
      rw [h s j, hj]
      rfl
  intro q
  induction q using Quotient.inductionOn with
  | h g => exact horbit g

theorem cosetAt_bijective (h : NativeAction) : Function.Bijective cosetAt := by
  apply (Fintype.bijective_iff_surjective_and_card cosetAt).mpr
  exact ⟨cosetAt_surjective h, by rw [Fintype.card_fin, card_elevenCoset]⟩

noncomputable def cosetEquiv (h : NativeAction) : Fin 720 ≃ ElevenCoset :=
  Equiv.ofBijective cosetAt (cosetAt_bijective h)

theorem leftIndex_injective (h : NativeAction) (s : Fin 2) :
    Function.Injective (leftIndex s) := by
  intro i j hij
  apply (cosetAt_bijective h).1
  have he := congrArg cosetAt hij
  rw [h s i, h s j] at he
  exact (MulAction.toPerm (generator s)).injective he

noncomputable def coordinates (h : NativeAction) :
    (ElevenCoset → ZMod 2) ≃ₗ[ZMod 2] Space :=
  LinearEquiv.piCongrLeft' (ZMod 2) (fun _ : ElevenCoset => ZMod 2)
    (cosetEquiv h).symm

theorem coordinates_apply (h : NativeAction) (v : ElevenCoset → ZMod 2) (j : Fin 720) :
    coordinates h v j = v (cosetAt j) := rfl

theorem coordinates_generator (h : NativeAction) (s : Fin 2) (v : ElevenCoset → ZMod 2) :
    coordinates h (cosetRepresentation (generator s) v) =
      (cosetMatrix s).mulVec (coordinates h v) := by
  ext r
  obtain ⟨j, rfl⟩ := Finite.surjective_of_injective (leftIndex_injective h s) r
  rw [coordinates_apply]
  change v ((generator s)⁻¹ • cosetAt (leftIndex s j)) = _
  rw [h s j, inv_smul_smul]
  change v (cosetAt j) =
    ∑ c : Fin 720, (if leftIndex s j = leftIndex s c then 1 else 0) * coordinates h v c
  simp only [(leftIndex_injective h s).eq_iff, ite_mul, one_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, coordinates_apply]

/-- The native action certificate has an actual representation-theoretic consumer. -/
noncomputable def cosetCoordinates (h : NativeAction) : CosetCoordinates where
  coordinates := coordinates h
  generator_coordinates := coordinates_generator h

end Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.CosetFlag.NativeBridge
