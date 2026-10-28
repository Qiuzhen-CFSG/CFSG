module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuCovers.Quotient
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuCovers.Ambient
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuCovers.BinaryProjection
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.MathieuEleven
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuTwentyThree
public import Theory.Mathieu.SchurMultipliers.FiniteCovers
public import Theory.Mathieu.SchurMultipliers.M23TwoKernelSource

/-!
# Surviving Mathieu covers and component intersections

The checked finite perfect-cover theorems kill the kernel of the original
map `L → L/O₂(L) → M₁₁` or `M₂₃`. Thus `O₂(L) = 1`, and that very map is
an equivalence. Apply the existing intersection theorems with the original
inner action of z. For M₂₃ this also supplies the actual normal E₁₆ kernel
and alternating quotient A₇ in the intersection.

Source: Aschbacher–Smith 1.1.5(3)(f), printed p.502, and 2.3.9(7)(d,f),
printed pp.525–526. The ambient exclusion of nontrivial M₂₂ two-covers
remains a separate obligation: innerness and fixation of a component Sylow
alone do not imply it. `M22Reduction` and `BinaryProjection` identify the
remaining binary and quartic covers with the original marked hexad models,
and apply the core-square theorem to the original binary inner projection.
-/

public section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement
open Subgroup Sporadic.Mathieu Theory.GroupTheory
open scoped Pointwise
variable {G : Type*} [Group G]
variable {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- No central two-kernel occurs over the actual M₁₁ quotient. -/
theorem mathieuEleven_twoCore_eq_bot (h : LocalSetup H L M S z)
    (e : (L ⧸ pCore 2 L) ≃* M11) : pCore 2 L = ⊥ := by
  let := h.finite
  let := h.quasisimple
  rw [← h.componentQuotientCover_ker e]
  exact SchurMultipliers.m11_cover_kernel_eq_bot (h.componentQuotientCover e)

/-- No central two-kernel occurs over the actual M₂₃ quotient. -/
theorem mathieuTwentyThree_twoCore_eq_bot (h : LocalSetup H L M S z)
    (e : (L ⧸ pCore 2 L) ≃* M23) : pCore 2 L = ⊥ := by
  let := h.finite
  rw [← h.componentQuotientCover_ker e]
  exact SchurMultipliers.M23TwoKernelSource.kernel_eq_bot (h.componentQuotientCover e)

/-- The M₁₁ branch starting from the two-core quotient in 1.1.5(3)(f):
the actual component model and the literal ambient centralizer intersection. -/
theorem mathieuEleven_cover_intersection (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .m11) :
    pCore 2 L = ⊥ ∧ ∃ eL : L ≃* M11,
      (∀ x : L, eL x = d.quotientIso (QuotientGroup.mk' (pCore 2 L) x)) ∧
      ∃ t : L, orderOf t = 2 ∧ IsConjugationProjection L z t ∧
        L ⊓ M = L ⊓ centralizer ({(t : G)} : Set G) := by
  have hk := mathieuEleven_twoCore_eq_bot h d.quotientIso
  let eL := twoCoreQuotientEquiv d.quotientIso hk
  exact ⟨hk, eL, fun _ => rfl,
    mathieuEleven_intersection h eL d.action d.conjugation d.inner⟩

/-- The M₂₃ branch from the literal quotient: model identification, heptad
stabilizer intersection, and the actual E₁₆-by-A₇ extension. -/
theorem mathieuTwentyThree_cover_intersection (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .m23) :
    pCore 2 L = ⊥ ∧ ∃ eL : L ≃* M23,
      (∀ x : L, eL x = d.quotientIso (QuotientGroup.mk' (pCore 2 L) x)) ∧
      (∃ B ∈ m23Blocks,
        (M.subgroupOf L).map eL.toMonoidHom = MulAction.stabilizer M23 B) ∧
      AlternatingBySixteen (M.subgroupOf L) 7 := by
  have hk := mathieuTwentyThree_twoCore_eq_bot h d.quotientIso
  let eL := twoCoreQuotientEquiv d.quotientIso hk
  exact ⟨hk, eL, fun _ => rfl,
    mathieuTwentyThree_intersection h eL d.action d.conjugation d.inner,
    mathieuTwentyThree_extension h eL d.action d.conjugation d.inner⟩

end CFSG.Quasithin.Chapter2.ComponentRefinement
end
