module
public import CFSG.Quasithin.ChapterD.Section01.MultipleFactors.ChiefEstimates

/-!
# From quadratic ratios on generators to D.1.3(j)

The local denominator is identified with the successive pointwise-kernel
index. The ratio definition then constructs every local inequality needed by
the generating filtration. A nontrivial action on the generated module forces
a nontrivial action on a generator, so the common lower ratio is finite before
we pass to real numbers. Equality propagates to a specified first generator.

Source: Aschbacher--Smith, D.1.3(b)--(j), printed pp.173--174. The remaining
source-specific conjugation step must supply the lower bound on each actual
generator's action image from q(G₁/C_G₁(V),V).
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterD.MultipleFactors
open Subgroup NoncentralChiefRefinement Representation Representation.BinaryOffender
open scoped ENNReal IsMulCommutative

private theorem subrepresentation_kernel_relIndex
    {H X : Type*} [Group H] [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) H X) (W : Subrepresentation ρ) (A : Subgroup H) :
    W.toRepresentation.ker.relIndex A = (subspaceKernel ρ W.toSubmodule A).relIndex A := by
  rw [← inf_relIndex_left A W.toRepresentation.ker]
  congr 1
  ext a
  constructor
  · rintro ⟨ha, hk⟩
    refine ⟨ha, fun w hw => ?_⟩
    exact congrArg Subtype.val (LinearMap.congr_fun hk ⟨w, hw⟩)
  · rintro ⟨ha, hk⟩
    refine ⟨ha, ?_⟩
    apply LinearMap.ext
    intro w
    exact Subtype.ext (hk w w.property)

variable {H : Type*} [Group H] [Finite H]
  (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
  (B : Subgroup H) [IsElementaryAbelian 2 B]
  (W : ℕ → Subrepresentation ((normalRepresentation U).comp B.subtype))

omit [Finite H] [IsElementaryAbelian 2 B] in
private theorem generator_quadratic
    (hquad : IsQuadratic (normalRepresentation U) B) (i : ℕ) (D : Subgroup B) :
    IsQuadratic (W i).toRepresentation D := by
  intro a _ b _ v
  exact Subtype.ext (hquad a a.property b b.property v)

/-- The generator ratio gives the exact local quotient inequality (c).
No local rank inequality is assumed. -/
theorem generator_local_bound (q : ℝ≥0∞) (hfinite : q ≠ ⊤)
    (hquad : IsQuadratic (normalRepresentation U) B) (i : ℕ)
    (hratio : q ≤ quadraticRatio (imageRepresentation (W i).toRepresentation)) :
    q.toReal * (Nat.log 2
      ((generatingKernel ((normalRepresentation U).comp B.subtype) W ⊤ (i + 1)).relIndex
        (generatingKernel ((normalRepresentation U).comp B.subtype) W ⊤ i)) : ℝ) ≤
      fixedCodim (W i).toRepresentation
        (generatingKernel ((normalRepresentation U).comp B.subtype) W ⊤ i) := by
  let D := generatingKernel ((normalRepresentation U).comp B.subtype) W ⊤ i
  let : IsElementaryAbelian 2 (⊤ : Subgroup B) :=
    IsElementaryAbelian.of_surjective (Subgroup.topEquiv : (⊤ : Subgroup B) ≃* B).symm.toMonoidHom
      (Subgroup.topEquiv : (⊤ : Subgroup B) ≃* B).symm.surjective
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_le (le_top : D ≤ ⊤)
  have h := quadratic_image_rank_bound_real (W i).toRepresentation
    (generator_quadratic U B W hquad i D) hfinite hratio
  rw [subrepresentation_kernel_relIndex, ← generatingKernel_succ] at h
  exact h

/-- Nontrivial action on the span constructs a nontrivial quadratic generator
action, excluding infinity without applying real arithmetic to infinity. -/
theorem generator_ratio_ne_top (q : ℝ≥0∞) (n : ℕ)
    (hgen : generatingSpan ((normalRepresentation U).comp B.subtype) W n = ⊤)
    (hquad : IsQuadratic (normalRepresentation U) B)
    (hnot : ¬ B ≤ centralizer (U : Set H))
    (hratio : ∀ i < n, q ≤ quadraticRatio (imageRepresentation (W i).toRepresentation)) :
    q ≠ ⊤ := by
  intro htop
  have hfix : ∀ i < n, (W i).toSubmodule ≤
      fixedSpace ((normalRepresentation U).comp B.subtype) ⊤ := by
    intro i hi
    have hkernel : (⊤ : Subgroup B) ≤ (W i).toRepresentation.ker := by
      by_contra hn
      let : IsElementaryAbelian 2 (⊤ : Subgroup B) :=
        IsElementaryAbelian.of_surjective (Subgroup.topEquiv : (⊤ : Subgroup B) ≃* B).symm.toMonoidHom
          (Subgroup.topEquiv : (⊤ : Subgroup B) ≃* B).symm.surjective
      have hf := quadraticRatio_image_ne_top (W i).toRepresentation hn
        (generator_quadratic U B W hquad i ⊤)
      exact hf (top_le_iff.mp (htop ▸ hratio i hi))
    intro v hv b
    exact congrArg Subtype.val (LinearMap.congr_fun (hkernel trivial) ⟨v, hv⟩)
  have hspan : ∀ m ≤ n, (generatingSpan ((normalRepresentation U).comp B.subtype) W m).toSubmodule ≤
      fixedSpace ((normalRepresentation U).comp B.subtype) ⊤ := by
    intro m hm
    induction m with
    | zero => exact bot_le
    | succ m ih => exact sup_le (ih (by omega)) (hfix m (by omega))
  have hall := hspan n le_rfl
  rw [hgen] at hall
  apply hnot
  rw [← normalRepresentation_ker U]
  intro b hb
  apply LinearMap.ext
  intro v
  exact hall (show v ∈ (⊤ : Subrepresentation ((normalRepresentation U).comp B.subtype)).toSubmodule
    from trivial) ⟨⟨b, hb⟩, trivial⟩

/-- Equation (j), with the local estimates proved from genuine quadratic ratios. -/
theorem generator_rank_bound (q : ℝ≥0∞) (n : ℕ) (hfinite : q ≠ ⊤)
    (hgen : generatingSpan ((normalRepresentation U).comp B.subtype) W n = ⊤)
    (hquad : IsQuadratic (normalRepresentation U) B)
    (hratio : ∀ i < n, q ≤ quadraticRatio (imageRepresentation (W i).toRepresentation)) :
    q.toReal * (Nat.log 2 (Nat.card (B ⧸ qrcActionKernel U B)) : ℝ) ≤
      fixedCodim (normalRepresentation U) B := by
  apply qrc_generating_bound U B W q.toReal n hgen
  exact fun i hi => generator_local_bound U B W q hfinite hquad i (hratio i hi)

/-- Equality at (j) forces equality on any chosen first generator. -/
theorem generator_first_equality (q : ℝ≥0∞) (n : ℕ) (hfinite : q ≠ ⊤) (hn : 0 < n)
    (hgen : generatingSpan ((normalRepresentation U).comp B.subtype) W n = ⊤)
    (hquad : IsQuadratic (normalRepresentation U) B)
    (hratio : ∀ i < n, q ≤ quadraticRatio (imageRepresentation (W i).toRepresentation))
    (heq : (fixedCodim (normalRepresentation U) B : ℝ) =
      q.toReal * (Nat.log 2 (Nat.card (B ⧸ qrcActionKernel U B)) : ℝ)) :
    (fixedCodim (W 0).toRepresentation ⊤ : ℝ) = q.toReal * (Nat.log 2
      (subspaceKernel ((normalRepresentation U).comp B.subtype) (W 0).toSubmodule ⊤).index : ℝ) := by
  apply qrc_generating_first_equality U B W q.toReal n hn hgen _ heq
  exact fun i hi => generator_local_bound U B W q hfinite hquad i (hratio i hi)

end CFSG.Quasithin.ChapterD.MultipleFactors
