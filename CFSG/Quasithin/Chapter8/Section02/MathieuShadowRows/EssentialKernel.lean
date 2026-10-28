module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.OddControlKernel
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.SpanImageReduction
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.CartanCubicLift
-- Internal source split: unfold the canonical core only to use its defining containment.
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The original essential kernel under odd-normalizer control

The full-span kernel lies in the essential kernel, hence in the original
maximal overlap H ∩ M, and centralizes the original seed V. Odd-normalizer
control and Frattini make it a two-group. The checked whole-span reduction
then makes the essential kernel a two-group, so it is exactly O₂(H).
This conclusion uses the additional original odd-normalizer hypothesis;
it is not asserted for general minimal parabolics.

The literal original M22-code application in M22CodeFaithfulChiefs discharges
that hypothesis. Source: Aschbacher--Smith 3.1.9(6), pp.577--578, used in
8.2.2(1), p.715, and odd-normalizer control 4.4.3, refs/quasithin.pdf.
-/

public section
open Subgroup Representation Representation.BinaryOffender MathieuCode.NormalizedShadowRows
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
variable {G : Type*} [Group G] [Finite G] {H M V : Subgroup G}

universe u

/-- A literal chief-image equivalence retains the full original action kernel. -/
theorem literal_chief_action_kernel_eq
    {D W W' : Type u} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    [AddCommGroup W'] [Module (ZMod 2) W'] [FiniteDimensional (ZMod 2) W']
    {ρ : Representation (ZMod 2) D W} {σ : Representation (ZMod 2) D W'}
    (e : LiteralChiefActionEquiv ρ σ) : (actionHom ρ).ker = (actionHom σ).ker := by
  ext x
  change actionHom ρ x = 1 ↔ actionHom σ x = 1
  rw [← e.map_action x, ← e.equiv.map_one, e.equiv.injective.eq_iff]

open Chapter3 ChapterB ChapterD NoncentralChiefRefinement
variable [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]
  {T : Sylow 2 G} {M₀ : Subgroup G} {hVH : V ≤ H}

set_option backward.isDefEq.respectTransparency false in
theorem essential_kernel_eq_twoCore
    (h : QrcHypotheses T M M₀ H V)
    (a : EssentialSeedAction H V (T.subtype h.right_mem.1.1.2) hVH)
    {A : Subgroup H} (ha : EssentialChiefActor a A)
    (s : SeriesOn ((conjugateSpan H V).subgroupOf H))
    (i : Fin s.series.length) (hi : ¬ s.Central i)
    (hcontrol : ∀ X : Subgroup G, X ≠ ⊥ →
      X ≤ M ⊓ centralizer (V : Set G) → Odd (Nat.card X) →
      normalizer (X : Set G) ≤ M) :
    a.projection.ker = pCore 2 H := by
  obtain ⟨r⟩ := essential_span_image_reduction a A ha s i hi
  let U := (conjugateSpan H V).subgroupOf H
  let τ := normalRepresentation U
  let q := actionHom τ
  have hker : q.ker ≤ a.projection.ker := reduction_kernel_le r
  have hmax : a.projection.ker ≤ (H ⊓ M).subgroupOf H := by
    rw [← h.intrinsic_maximal_eq_intersection a.original_minimal]
    exact (minimalParabolic_reduced_image _ a.original_minimal a.projection
      a.projection_surjective a.twoCore_eq_bot a.projection_kernel_ne_top).1.trans
      (normalCore_le _)
  have hq2 : IsPGroup 2 q.ker :=
    normal_centralizing_kernel_twoGroup q.ker
      (by rintro _ ⟨x,hx,rfl⟩; exact (hmax (hker hx)).2)
      (by rintro _ ⟨x,hx,rfl⟩; exact span_action_kernel_centralizes hVH x hx)
      h.right_mem.1.2 hcontrol
  exact reduced_twoGroup_kernel_eq_core a.projection a.projection_surjective
    a.twoCore_eq_bot (reduction_kernel_isPGroup r hq2)

end CFSG.Quasithin.Chapter8.MathieuShadowRows
