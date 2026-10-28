module

public import Theory.SpecificGroups.PSL3Four.AnisotropicRootRecognition.Coordinates
public import Theory.SpecificGroups.PSL3Four.AnisotropicRootRecognition.FiniteCriterion
public import Theory.SpecificGroups.PSL3Four.AnisotropicRootRecognition.IntrinsicCoordinates
public import Theory.SpecificGroups.PSL3Four.AnisotropicRootRecognition.RootRealization

/-!
# Recognizing UT₃(F₄) from anisotropic factors and balanced square fibers

The intrinsic factor geometry supplies marked binary normal forms. The
centralizer condition and balanced nonidentity central square fibers force
one of six explicit multiplication laws, each isomorphic to the literal
upper unitriangular group over `GaloisField 2 2`. Composing these actual
multiplicative equivalences recognizes the original group without assuming
coordinates, a tensor decomposition, or an action of its normalizer.

Source motivation: Aschbacher, *Sporadic Groups* (1994), proof of 46.14,
printed pp.257–258, using 8.15 and 46.2–46.3.
-/

public section
namespace Theory.GroupTheory.AnisotropicRecognition

/-- The exact finite reduction for any chosen marked normal forms of the
intrinsic factor geometry. -/
theorem sixCases_of_coordinates {K : Type*} [Group K]
    (F : AnisotropicFactors K) (C : MarkedCoordinates F)
    (h : ∀ c d : Subgroup.center K, c ≠ 1 → d ≠ 1 →
      Nat.card {x : K // x ^ 2 = (c : K)} = Nat.card {x : K // x ^ 2 = (d : K)}) :
    SixCases C.matrix :=
  sixCases_of_balanced C.matrix (firstNondegenerate_of_coordinates F C)
    (balanced_of_coordinates F C h)

/-- Anisotropic factors and balanced nonidentity central square fibers
determine the actual multiplication of UT₃(F₄). All intermediate marked
coordinates are constructed from the intrinsic factor hypotheses. -/
theorem rootEquiv_of_balanced {K : Type*} [Group K] [Finite K]
    (F : AnisotropicFactors K)
    (h : ∀ c d : Subgroup.center K, c ≠ 1 → d ≠ 1 →
      Nat.card {x : K // x ^ 2 = (c : K)} = Nat.card {x : K // x ^ 2 = (d : K)}) :
    Nonempty (K ≃* Matrix.PSL3Four.RootNormalizerModel.Root) := by
  obtain ⟨C⟩ := nonempty_markedCoordinates F
  exact rootEquiv_of_coordinates F C h

end Theory.GroupTheory.AnisotropicRecognition
