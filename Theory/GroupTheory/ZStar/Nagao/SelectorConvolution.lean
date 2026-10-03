module

public import Theory.Character.ModularBlock.ProjectorTrace
public import Theory.GroupTheory.ZStar.CanonicalLocalCoreSupport

/-!
# Selector Convolution

Convolution by the ordinary principal-block idempotent is the projection
onto the principal-block character summands of a class function. Expand the
class function in the complete irreducible character family, use the
selector's scalar action on each representation, and interchange the finite
sums. This is the ordinary-character calculation relating complement
coefficients to the outside-principal-block part of an involution section.

Ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/CharacterwiseProjection.lean` (revision `c3503435`).
-/

public section

noncomputable section

open scoped BigOperators

namespace Glauberman.ZStar.CharacterwiseProjection

open ModularBlock PrincipalBlockConstruction
open LocalBlockSection ModularBlock.CharacterwiseProjection

universe u v

attribute [local instance] Fintype.ofFinite

variable {G : Type u} [Group G] [finG : Finite G]

/-! Convolution by the ordinary principal-block idempotent is the
orthogonal projection on class functions. -/

theorem principalBlockElement_convolution_projection
    {H : Type v} [Group H] [Finite H]
    (e : PrincipalCongruenceBlockData H)
    (f : ConjClassFunction H) (x : H) :
    ∑ h : H,
        (BlockOrthogonality.principalBlockElement e).coeff h *
          f (ConjClasses.mk (x * h)) =
      LocalBlockSection.localPrincipalBlockProjection e f
        (ConjClasses.mk x) := by
  classical
  rw [LocalBlockSection.localPrincipalBlockProjection_apply]
  have hexpand (y : H) :
      f (ConjClasses.mk y) =
        ∑ j : e.I,
          classFunctionInner f (e.chi j) *
            e.chi j (ConjClasses.mk y) := by
    simpa using completeFamily_apply_eq_sum_inner
      e.complete f (ConjClasses.mk y)
  have hchar_sum (j : e.I) :
      ∑ h : H,
          (BlockOrthogonality.principalBlockElement e).coeff h *
            e.chi j (ConjClasses.mk (x * h)) =
        (if j ∈ e.block then (1 : ℂ) else 0) *
          e.chi j (ConjClasses.mk x) := by
    rcases (e.complete.1 j).1 with ⟨n, rho, hrho⟩
    have htrace := trace_left_groupAlgebra_mul rho x
      (BlockOrthogonality.principalBlockElement e)
    have haction := BlockOrthogonality.principalBlockElement_action
      e j rho hrho
    have hchi (y : H) :
        e.chi j (ConjClasses.mk y) = rho.character y := by
      rw [hrho]
      rfl
    calc
      _ = LinearMap.trace ℂ (Fin n → ℂ)
            (rho x * rho.asAlgebraHom
              (BlockOrthogonality.principalBlockElement e)) := by
          simp_rw [hchi]
          exact htrace.symm
      _ = LinearMap.trace ℂ (Fin n → ℂ)
            (rho x * ((if j ∈ e.block then (1 : ℂ) else 0) •
              (1 : Module.End ℂ (Fin n → ℂ)))) := by rw [haction]
      _ = _ := by
        by_cases hj : j ∈ e.block
        · simp only [hj, if_true, one_smul, mul_one]
          exact (hchi x).symm.trans (one_mul _).symm
        · simp [hj]
  calc
    ∑ h : H,
          (BlockOrthogonality.principalBlockElement e).coeff h *
            f (ConjClasses.mk (x * h)) =
        ∑ j : e.I,
          classFunctionInner f (e.chi j) *
            (∑ h : H,
              (BlockOrthogonality.principalBlockElement e).coeff h *
                e.chi j (ConjClasses.mk (x * h))) := by
      simp_rw [hexpand, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _hj
      apply Finset.sum_congr rfl
      intro h _hh
      ring
    _ = ∑ j : e.I,
          if j ∈ e.block then
            classFunctionInner f (e.chi j) *
              e.chi j (ConjClasses.mk x)
          else 0 := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [hchar_sum]
      by_cases hj : j ∈ e.block <;> simp [hj]
    _ = ∑ j ∈ e.block,
          classFunctionInner f (e.chi j) *
            e.chi j (ConjClasses.mk x) := by
      simp


end Glauberman.ZStar.CharacterwiseProjection

