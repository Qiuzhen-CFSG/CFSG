module
public import Theory.Representation.SL2OrthogonalCover.OuterSemilinear
public import Theory.Representation.CentralCoverOriginalAction
public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms.FieldAction
import Mathlib.Tactic.FinCases

/-!
# Lifting a coherent field alignment to the full orthogonal cover

An alignment of the natural module with a coefficient-field action has a
unique lift to the universal orthogonal cover. The two composite lifts of the
original actor agree on the literal projection; commutator generation then
identifies them. Thus the same quotient-group marking aligns the full module,
including its central radical, with entrywise field action.

The coordinate action also commutes with field inclusion, which identifies
the fixed cover with the orthogonal cover over the fixed field. This is the
full-cover descent used in Aschbacher–Smith, Lemma 2.4.12(2), printed p.532.
-/

public section
noncomputable section
namespace Representation.SL2OrthogonalCover
open Matrix Representation.OneCohomology Representation.OneCohomology.CentralCoverOriginalAction
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Finite F] [CharP F 2] in
/-- Entrywise action of the marked coefficient automorphism on the full cover. -/
def coefficientEquiv (σ : F ≃+* F) : Space F ≃ₗ[ZMod 2] Space F :=
  let e : Space F ≃+ Space F :=
    { toFun v i := σ (v i)
      invFun v i := σ.symm (v i)
      left_inv v := by ext i; exact σ.symm_apply_apply _
      right_inv v := by ext i; exact σ.apply_symm_apply _
      map_add' v w := by ext i; exact map_add σ _ _ }
  { e with map_smul' := fun c v => ZMod.map_smul e c v }

omit [Finite F] [CharP F 2] in
@[simp] theorem coefficientEquiv_apply (σ : F ≃+* F) (u : Space F) (i : Fin 3) :
    coefficientEquiv σ u i = σ (u i) := by rfl

omit [Algebra (ZMod 2) F] in
private theorem root_map (σ : F ≃+* F) (x : F) : σ (root x) = root (σ x) := by
  apply CharTwo.sq_injective
  change (σ (root x)) ^ 2 = (root (σ x)) ^ 2
  rw [← map_pow, sq_root, sq_root]

/-- The coordinate field action intertwines the actual orthogonal formula. -/
theorem coefficientEquiv_intertwining (σ : F ≃+* F) (g : SL F) (u : Space F) :
    coefficientEquiv σ (action g u) = action (Theory.PSL2.sl2FieldAut σ g) (coefficientEquiv σ u) := by
  ext i
  fin_cases i
  · change σ (u 0 + root (g.val 0 0 * g.val 1 0) * u 1 +
        root (g.val 0 1 * g.val 1 1) * u 2) =
      σ (u 0) + root (σ (g.val 0 0) * σ (g.val 1 0)) * σ (u 1) +
        root (σ (g.val 0 1) * σ (g.val 1 1)) * σ (u 2)
    simp only [map_add, map_mul, root_map]
  · change σ (g.val 0 0 * u 1 + g.val 0 1 * u 2) =
      σ (g.val 0 0) * σ (u 1) + σ (g.val 0 1) * σ (u 2)
    simp only [map_add, map_mul]
  · change σ (g.val 1 0 * u 1 + g.val 1 1 * u 2) =
      σ (g.val 1 0) * σ (u 1) + σ (g.val 1 1) * σ (u 2)
    simp only [map_add, map_mul]

omit [Algebra (ZMod 2) F] in
/-- The orthogonal formula respects the literal field inclusion. -/
theorem action_map {K : Type*} [Field K] [Finite K] [CharP K 2]
    (f : K →+* F) (g : SL K) (u : Space K) :
    (fun i => f (action g u i)) =
      action (Matrix.SpecialLinearGroup.map f g) (fun i => f (u i)) := by
  have hr (x : K) : f (root x) = root (f x) := by
    apply CharTwo.sq_injective
    change (f (root x)) ^ 2 = (root (f x)) ^ 2
    rw [← map_pow, sq_root, sq_root]
  ext i
  fin_cases i
  · change f (u 0 + root (g.val 0 0 * g.val 1 0) * u 1 +
        root (g.val 0 1 * g.val 1 1) * u 2) =
      f (u 0) + root (f (g.val 0 0) * f (g.val 1 0)) * f (u 1) +
        root (f (g.val 0 1) * f (g.val 1 1)) * f (u 2)
    simp only [map_add, map_mul, hr]
  · change f (g.val 0 0 * u 1 + g.val 0 1 * u 2) =
      f (g.val 0 0) * f (u 1) + f (g.val 0 1) * f (u 2)
    simp only [map_add, map_mul]
  · change f (g.val 1 0 * u 1 + g.val 1 1 * u 2) =
      f (g.val 1 0) * f (u 1) + f (g.val 1 1) * f (u 2)
    simp only [map_add, map_mul]

/-- An ambient alignment of the natural quotient lifts over its literal
projection and aligns the full orthogonal actor with the same field action. -/
theorem exists_alignment_lift (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (a : MulAut (SL F)) (E : Space F ≃ₗ[ZMod 2] Space F)
    (hE : ∀ g u, E (action g u) = action (a g) (E u))
    (e : Plane F ≃ₗ[ZMod 2] Plane F)
    (hoverE : ∀ u, projection (E u) = e (projection u))
    (σ : F ≃+* F) (β : MulAut (SL F)) (B : Plane F ≃ₗ[ZMod 2] Plane F)
    (hB : ∀ g v, B (natural g v) = natural (β g) (B v))
    (hβ : ∀ g, β (a g) = Theory.PSL2.sl2FieldAut σ (β g))
    (hBe : ∀ v i, B (e v) i = σ (B v i)) :
    ∃ A : Space F ≃ₗ[ZMod 2] Space F,
      (∀ g u, A (action g u) = action (β g) (A u)) ∧
      (∀ u, projection (A u) = B (projection u)) ∧
      ∀ u, A (E u) = coefficientEquiv σ (A u) := by
  have hp := binaryProjection_isCover (card_gt_two n hn hF)
  have hd : Module.finrank (ZMod 2) (binaryProjection (F := F)).toLinearMap.ker =
      Module.finrank (ZMod 2) (H1 (binaryNatural (F := F)).dual) := by
    rw [binary_kernel_finrank n hF, binary_dual_H1_finrank n hn hF]
  obtain ⟨A, hA, hoverA⟩ := exists_lift (binaryProjection (F := F)) hp hd β B hB
  have hA' (g : SL F) (u : Space F) : A (action g u) = action (β g) (A u) := hA g u
  refine ⟨A, hA, hoverA, ?_⟩
  have heq : A.toLinearMap.comp E.toLinearMap =
      (coefficientEquiv σ).toLinearMap.comp A.toLinearMap := by
    apply lift_unique (binaryAction (F := F))
      ((binaryAction (F := F)).comp (β * a).toMonoidHom) hp.2.2
      (binaryProjection (F := F)).toLinearMap
      (fun u hu g => hp.2.1 hu ((β * a) g))
    · intro g u
      change A (E (action g u)) = action (β (a g)) (A (E u))
      rw [hE, hA']
    · intro g u
      change coefficientEquiv σ (A (action g u)) = action (β (a g)) (coefficientEquiv σ (A u))
      rw [hA', hβ, coefficientEquiv_intertwining]
    · intro u
      change projection (A (E u)) = projection (coefficientEquiv σ (A u))
      have hoverA' (v : Space F) : projection (A v) = B (projection v) := hoverA v
      rw [hoverA', hoverE]
      ext i
      rw [hBe]
      have hi := congrFun (hoverA' u) i
      fin_cases i <;> exact congrArg σ hi.symm
  exact fun u => LinearMap.congr_fun heq u
end Representation.SL2OrthogonalCover
