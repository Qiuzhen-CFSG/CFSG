module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.PreGeometry
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.CubicRootGeometry.Contract

/-!
# The remaining central-cover lifting output

The source residual preparation constructs the planes, the E₉ quotient,
both full residuals and their actual diagonal actors. To apply the existing
centre argument it remains to lift projective commutator coverage and fixed
points through the central two-kernel. This output deliberately has no full
automorphism-coverage clause: that enters only the later I=L Y_D S product.

`CentralLift` must construct this output from `PreparedResiduals`, the exact
earlier local inputs and the intrinsic `FourSylowRootCalculations` output.
In particular O₂(D) must first be shown to centralize Z(L), making the
centre action factor through D/O₂(D). Neither this record nor its fields
are standing source hypotheses or completed source mathematics.

Source: Aschbacher--Smith, proof of 15.3.38, printed p.1136.
-/

@[expose] public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
variable {G : Type*} [Group G]

/-- Output of the intrinsic calculations transported to the actual Sylow and
the original quotient marking. The ProjectiveRoots producer must prove the
plane-image equality from normalization and cardinality, not from an arbitrary
inner conjugate in `RootInPlane`. -/
structure ProjectiveRootData (S L D W₂ : Subgroup G) {q : ℕ}
    (c : ProjectiveMarking L q) where
  sylow : Sylow 2 PSL(3,c.F)
  sylow_image : (S.subgroupOf L).map (projectiveMap c) = sylow
  plane_image : (W₂.subgroupOf L).map (projectiveMap c) =
    (center sylow).map (sylow : Subgroup PSL(3,c.F)).subtype
  cubic : ∀ z ∈ D, c.Diagonal z → ∀ α : MulAut PSL(3,c.F), c.Realizes z α →
    (sylow : Subgroup PSL(3,c.F)) ⊓ α.fixedSubgroup =
        (W₂.subgroupOf L).map (projectiveMap c) ∧
      commutatorSubgroup (zpowers α) PSL(3,c.F) (sylow : Subgroup PSL(3,c.F)) = sylow

/-- Output of the projective-to-central-cover lifting argument. -/
structure PrecentreCalculations (S L D W₂ : Subgroup G) : Prop where
  normalizes_sylow : D ≤ normalizer (S ⊓ L : Subgroup G)
  commutator : ⁅S ⊓ L, D⁆ = S ⊓ L
  root_fixed : (S ⊓ L) ⊓ centralizer (D : Set G) ≤ W₂ ⊔ centerImage L
  sylow_fixed : S ⊓ centralizer (D : Set G) ≤
    W₂ ⊔ (S ⊓ centralizer (L : Set G))

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
