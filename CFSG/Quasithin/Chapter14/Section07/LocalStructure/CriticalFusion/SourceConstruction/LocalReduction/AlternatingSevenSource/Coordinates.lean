module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.Quotients

/-!
# Coordinates for the original proper local quotient

The section and projection here keep both literal kernels: O₂(I) in the
actor and the chosen invariant subspace in U_I/V₁. They provide a common
interface for the natural and four-plus-dual exclusions in 14.7.50.
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}
  {F : InvariantFlag T V 3} {I : Subgroup G} [IsElementaryAbelian 2 (F.UH I)]

/-- The actual U_I/V₁ coordinates, with the action pulled back to I. -/
def localQuotientSection (a : LocalQuotientAction I (F.UH I) (F.Vi 1)) :
    BinaryConjugationSection I (F.UH I) (F.Vi 1)
      (a.representation.comp (QuotientGroup.mk' (pCore 2 I))) where
  section_le := a.le_local
  kernel_le := a.kernel_le
  normalized := a.normalizes
  coordinates := {
    toFun z := Multiplicative.ofAdd (Additive.ofMul
      (QuotientGroup.mk' ((F.Vi 1).subgroupOf (F.UH I)) z))
    map_one' := (QuotientGroup.mk' _).map_one
    map_mul' := (QuotientGroup.mk' _).map_mul }
  onto := QuotientGroup.mk'_surjective _
  kernel_eq := QuotientGroup.ker_mk' _
  equivariant i z := (a.conjugation i z).symm

/-- Projection to the selected quotient, equivariant for the actual local. -/
def localQuotientProjection (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
    (N : Subrepresentation a.representation) :
    Representation.IntertwiningMap (a.representation.comp (QuotientGroup.mk' (pCore 2 I)))
      (N.quotientRepresentation.comp (QuotientGroup.mk' (pCore 2 I))) where
  toLinearMap := N.toSubmodule.mkQ
  isIntertwining' _ := rfl

omit [Finite G] in
/-- Properness of the chosen subrepresentation is precisely properness of
the kernel in the original coordinates. -/
theorem localQuotientProjection_ker_ne_top
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
    (N : Subrepresentation a.representation) (hN : N ≠ ⊤) :
    (localQuotientProjection a N).toLinearMap.ker ≠ ⊤ := by
  change N.toSubmodule.mkQ.ker ≠ ⊤
  rw [Submodule.ker_mkQ]
  intro he
  exact hN (Subrepresentation.toSubmodule_injective he)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
