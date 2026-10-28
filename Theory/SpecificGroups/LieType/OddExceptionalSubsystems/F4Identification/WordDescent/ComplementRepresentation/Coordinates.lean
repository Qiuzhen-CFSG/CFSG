module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.Eigenspaces
public import Mathlib.LinearAlgebra.Pi

/-!
# Sparse coordinates for the complementary diagram space

The differences of paired coordinate vectors span the minus-one eigenspace
when 2 is invertible. Consequently an equality of actions can be checked on
these explicit vectors, using differences of columns of the original E6
matrices. This test includes characteristic three and uses no irreducibility.

The local representation construction in `ComplementRepresentation` consumes
this test, retaining the literal pinned involution and all generator parameters.
Source: the diagram decomposition for GLS3 §§2.3, 2.6 and the folded inclusion
in Aschbacher--Smith A.2.17, printed p.39.
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
open WordDescent Theory.AlgebraicGroup.StandardRootSystem
open scoped Matrix
attribute [local instance] Classical.decEq

variable (F : Type*) [Field F]

/-- Antisymmetrization into the literal complement. -/
def antisymmetrize : Space F →ₗ[F] complementSpace F where
  toFun v := ⟨v - diagramLinear F v, by
    simp only [mem_eigenspace, map_sub, diagramLinear_twice, neg_smul, one_smul]
    abel⟩
  map_add' v w := by
    apply Subtype.ext
    change (v + w) - diagramLinear F (v + w) = _
    rw [map_add]
    change (v + w) - (diagramLinear F v + diagramLinear F w) =
      (v - diagramLinear F v) + (w - diagramLinear F w)
    abel
  map_smul' c v := by
    apply Subtype.ext
    exact (by simp only [map_smul, smul_sub] :
      c • v - diagramLinear F (c • v) = c • (v - diagramLinear F v))

/-- A difference of two paired E6 coordinate vectors. It is zero at a fixed index. -/
def antiVector (j : Index) : complementSpace F := antisymmetrize F (Pi.single j 1)

theorem diagramLinear_single (j : Index) :
    diagramLinear F (Pi.single j 1) = Pi.single (typeE6PinnedIndexEquiv j) 1 := by
  ext i
  have hi : typeE6PinnedIndexEquiv i = j ↔ i = typeE6PinnedIndexEquiv j := by
    constructor
    · intro h
      simpa only [typeE6PinnedIndexEquiv_twice] using congrArg typeE6PinnedIndexEquiv h
    · intro h
      simpa only [typeE6PinnedIndexEquiv_twice] using congrArg typeE6PinnedIndexEquiv h
  simp only [diagramLinear, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply, hi]

theorem antiVector_val (j : Index) :
    (antiVector F j : Space F) =
      Pi.single j 1 - Pi.single (typeE6PinnedIndexEquiv j) 1 := by
  change Pi.single j 1 - diagramLinear F (Pi.single j 1) = _
  rw [diagramLinear_single]

theorem antisymmetrize_surjective (htwo : (2 : F) ≠ 0) :
    Function.Surjective (antisymmetrize F) := by
  intro v
  refine ⟨(2 : F)⁻¹ • (v : Space F), ?_⟩
  apply Subtype.ext
  change (2 : F)⁻¹ • (v : Space F) -
    diagramLinear F ((2 : F)⁻¹ • (v : Space F)) = v
  rw [map_smul, v.property]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Equality on the explicit antisymmetric coordinate vectors detects linear maps. -/
theorem linearMap_ext_antiVector (htwo : (2 : F) ≠ 0)
    {V : Type*} [AddCommGroup V] [Module F V]
    (f g : complementSpace F →ₗ[F] V)
    (h : ∀ j : Index, f (antiVector F j) = g (antiVector F j)) : f = g := by
  have hc : f.comp (antisymmetrize F) = g.comp (antisymmetrize F) := by
    apply LinearMap.pi_ext
    intro j x
    have hs : Pi.single j x = x • (Pi.single j 1 : Space F) := by
      rw [← Pi.single_smul]
      simp
    simp only [LinearMap.comp_apply, hs, map_smul]
    exact congrArg (x • ·) (h j)
  apply LinearMap.ext
  intro v
  obtain ⟨w, rfl⟩ := antisymmetrize_surjective F htwo v
  exact LinearMap.congr_fun hc w

/-- The actual folded action is computed by a difference of its original columns. -/
theorem eigenspaceAction_antiVector (g : splitSubgroup F) (j : Index) :
    (eigenspaceAction F (-1) g (antiVector F j) : Space F) =
      fun i => foldedMatrix F g i j - foldedMatrix F g i (typeE6PinnedIndexEquiv j) := by
  rw [eigenspaceAction_apply, antiVector_val, Matrix.mulVec_sub]
  simp only [Matrix.mulVec_single_one]
  rfl

/-- A sparse coordinate check proves the literal marked action equation. -/
theorem linearEquiv_eq_eigenspaceAction (htwo : (2 : F) ≠ 0)
    (e : complementSpace F ≃ₗ[F] complementSpace F) (g : splitSubgroup F)
    (h : ∀ j i : Index, (e (antiVector F j) : Space F) i =
      foldedMatrix F g i j - foldedMatrix F g i (typeE6PinnedIndexEquiv j)) :
    e = eigenspaceAction F (-1) g := by
  apply LinearEquiv.toLinearMap_injective
  apply linearMap_ext_antiVector F htwo
  intro j
  apply Subtype.ext
  funext i
  exact (h j i).trans (congrFun (eigenspaceAction_antiVector F g j) i).symm

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
