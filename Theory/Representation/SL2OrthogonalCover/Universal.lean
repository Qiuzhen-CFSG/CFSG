module
public import Theory.Representation.SL2OrthogonalCover
public import Theory.Representation.SL2NaturalFirstCohomology
public import Theory.Representation.FirstCohomologyDuality.QuotientGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The universal binary SL₂ cover and arbitrary central quotients

The three-dimensional orthogonal cover remains a cover after restricting
scalars to F₂. Composing the determinant pairing with a binary linear functional
that takes 1 to 1 proves binary self-duality of the marked natural plane.
Thus I.1.6 gives the dual H¹ dimension, exactly the dimension of the central
kernel of our model. The maximal-kernel comparison identifies it with the
actual cohomological universal binary cover over the original projection.

Root commutators and centrality descend through the resulting surjections
to arbitrary binary covers, without making their kernels into F-subspaces.

Source: Aschbacher–Smith, Remark I.1.5 and Lemmas I.1.6, I.2.3(3), printed
pp.408, 413 of the combined manuscript (1 March 2004).
-/

public section
noncomputable section
namespace Representation.SL2OrthogonalCover
open Matrix Matrix.SpecialLinearGroup Representation.OneCohomology
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
section Binary
variable [Algebra (ZMod 2) F]

abbrev binaryNatural : Representation (ZMod 2) (SL F) (Plane F) := restrictScalars natural
abbrev binaryAction : Representation (ZMod 2) (SL F) (Space F) := restrictScalars action
/-- Scalar restriction retains the literal projection onto the natural plane. -/
@[expose] def binaryProjection : (binaryAction (F := F)).IntertwiningMap (binaryNatural (F := F)) :=
  restrictCoverMap (k := ZMod 2) projection
lemma binaryProjection_isCover (hF : 2 < Nat.card F) :
    IsCover (binaryProjection (F := F)) := by
  exact isCover_restrictScalars (k := ZMod 2) (projection (F := F)) (projection_isCover hF)

private def wedge (v w : Plane F) : F := v 0 * w 1 - v 1 * w 0
omit [Finite F] [CharP F 2] [Algebra (ZMod 2) F] in
private lemma wedge_invariant (g : SL F) (v w : Plane F) :
    wedge (natural g v) (natural g w) = wedge v w := by
  have hd : g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0 = 1 := by
    simpa only [det_fin_two] using g.property
  calc
    _ = (g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0) * wedge v w := by
      simp only [wedge, natural, specialLinearNatural_apply, mulVec, dotProduct, Fin.sum_univ_two]
      ring
    _ = _ := by rw [hd, one_mul]

/-- Any ground-field functional taking 1 to 1 gives a nondegenerate determinant pairing. -/
private def fieldFunctional : F →ₗ[ZMod 2] ZMod 2 :=
  Classical.choose (Module.Projective.exists_dual_eq_one (ZMod 2) (one_ne_zero : (1 : F) ≠ 0))
omit [Finite F] [CharP F 2] in
private lemma fieldFunctional_one : fieldFunctional (1 : F) = 1 :=
  Classical.choose_spec (Module.Projective.exists_dual_eq_one (ZMod 2) (one_ne_zero : (1 : F) ≠ 0))

def binaryPairing : Plane F →ₗ[ZMod 2] Module.Dual (ZMod 2) (Plane F) where
  toFun v := {
    toFun w := fieldFunctional (wedge v w)
    map_add' w x := by
      rw [show wedge v (w + x) = wedge v w + wedge v x by
        simp only [wedge, Pi.add_apply]; ring, map_add]
    map_smul' c w := by
      change fieldFunctional (wedge v (c • w)) = c • fieldFunctional (wedge v w)
      rw [show wedge v (c • w) = c • wedge v w by
        simp [wedge, Pi.smul_apply, smul_sub], map_smul] }
  map_add' v w := by
    apply LinearMap.ext
    intro x
    change fieldFunctional (wedge (v + w) x) =
      fieldFunctional (wedge v x) + fieldFunctional (wedge w x)
    rw [show wedge (v + w) x = wedge v x + wedge w x by
      simp only [wedge, Pi.add_apply]; ring, map_add]
  map_smul' c v := by
    apply LinearMap.ext
    intro w
    change fieldFunctional (wedge (c • v) w) = c • fieldFunctional (wedge v w)
    rw [show wedge (c • v) w = c • wedge v w by
      simp [wedge, Pi.smul_apply, smul_sub], map_smul]

omit [Finite F] [CharP F 2] in
lemma binaryPairing_injective : Function.Injective (binaryPairing (F := F)) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro v hv
  have hz (w : Plane F) : fieldFunctional (wedge v w) = 0 := LinearMap.congr_fun hv w
  have h0 : v 0 = 0 := by
    by_contra hn
    have h := hz ![0, (v 0)⁻¹]
    simp only [wedge, cons_val_one, cons_val_zero, mul_inv_cancel₀ hn,
      mul_zero, sub_zero, fieldFunctional_one] at h
    exact one_ne_zero h
  have h1 : v 1 = 0 := by
    by_contra hn
    have h := hz ![-(v 1)⁻¹, 0]
    simp only [wedge, cons_val_one, cons_val_zero, mul_zero, mul_neg,
      mul_inv_cancel₀ hn, sub_neg_eq_add, zero_add, fieldFunctional_one] at h
    exact one_ne_zero h
  change v = 0
  ext i; fin_cases i <;> assumption

/-- Binary self-duality uses the actual SL₂ marking, for every finite field. -/
def binarySelfDual : Plane F ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (Plane F) :=
  LinearEquiv.ofBijective binaryPairing ⟨binaryPairing_injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := ZMod 2) (V := Plane F)).symm).mp binaryPairing_injective⟩
omit [CharP F 2] in
lemma binarySelfDual_equivariant (g : SL F) (v : Plane F) :
    (binarySelfDual (F := F)) ((binaryNatural (F := F)) g v) = (binaryNatural (F := F)).dual g ((binarySelfDual (F := F)) v) := by
  apply LinearMap.ext
  intro w
  change fieldFunctional (wedge (natural g v) w) =
    fieldFunctional (wedge v (natural g⁻¹ w))
  apply congrArg fieldFunctional
  have h := wedge_invariant g v (natural g⁻¹ w)
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
  exact h

lemma binary_dual_H1_finrank (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n) :
    Module.finrank (ZMod 2) (H1 (binaryNatural (F := F)).dual) = n := by
  let e := H1Congr (k := ZMod 2) (binaryNatural (F := F)) (binaryNatural (F := F)).dual (MulEquiv.refl (SL F))
    (binarySelfDual (F := F)) (fun g v => binarySelfDual_equivariant g v)
  rw [← e.finrank_eq]
  exact SL2NaturalH1.finrank_restrict_eq n hn hF

lemma binary_kernel_finrank (n : ℕ) (hF : Nat.card F = 2 ^ n) :
    Module.finrank (ZMod 2) (binaryProjection (F := F)).toLinearMap.ker = n := by
  have he : (binaryProjection (F := F)).toLinearMap.ker =
      ((projection (F := F)).toLinearMap.ker).restrictScalars (ZMod 2) := rfl
  rw [he, projection_kernel,
    ((Submodule.restrictScalarsEquiv (ZMod 2) F (Space F) (form (F := F)).polarBilin.ker).restrictScalars (ZMod 2)).finrank_eq]
  rw [← Module.finrank_mul_finrank (ZMod 2) F (form (F := F)).polarBilin.ker,
    radical_dimension, mul_one]
  exact SL2NaturalH1.field_finrank n hF

omit [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F] in
lemma card_gt_two (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n) : 2 < Nat.card F := by
  rw [hF]
  exact (by decide : 2 < 2 ^ 2).trans_le (Nat.pow_le_pow_right (by decide) hn)

/-- The orthogonal action is the genuine universal binary cover, equivariantly
and over its natural projection. No F-structure on an arbitrary cover is used. -/
lemma universal_equiv (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n) :
    ∃ e : Module.Dual (ZMod 2) (cocycles (binaryNatural (F := F)).dual) ≃ₗ[ZMod 2] Space F,
      (∀ g u, e ((universalAction (binaryNatural (F := F)).dual).dual g u) = (binaryAction (F := F)) g (e u)) ∧
      ∀ u, (binaryProjection (F := F)) (e u) = universalCoverProjection (binaryNatural (F := F)) u := by
  have hd : Module.finrank (ZMod 2) (binaryProjection (F := F)).toLinearMap.ker =
      Module.finrank (ZMod 2) (H1 (binaryNatural (F := F)).dual) := by
    rw [binary_kernel_finrank n hF, binary_dual_H1_finrank n hn hF]
  exact exists_equiv_universalCover_of_finrank_ker_eq (k := ZMod 2)
    (ρ := binaryNatural (F := F)) (σ := binaryAction (F := F)) (binaryProjection (F := F))
    (binaryProjection_isCover (card_gt_two n hn hF)) hd

omit [Finite F] [CharP F 2] in
lemma natural_fixed : fixed (binaryNatural (F := F)) = ⊥ := by
  apply bot_unique
  intro v hv
  have h1 := congrFun (hv (upper 1)) 0
  have h0 := congrFun (hv (lower 1)) 1
  change v = 0
  ext i
  fin_cases i
  · simpa [binaryNatural, natural, restrictScalars, specialLinearNatural_apply,
      lower, transvection_coe, mulVec, dotProduct, Fin.sum_univ_two] using h0
  · simpa [binaryNatural, natural, restrictScalars, specialLinearNatural_apply,
      upper, transvection_coe, mulVec, dotProduct, Fin.sum_univ_two] using h1

/-- The literal first line and its inverse image make sense over F₂. -/
@[expose] def firstLine : Submodule (ZMod 2) (Plane F) := (LinearMap.proj 1).ker

@[expose] def firstPreimage {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) (SL F) W}
    (p : σ.IntertwiningMap (binaryNatural (F := F))) : Submodule (ZMod 2) W := (firstLine (F := F)).comap p.toLinearMap

lemma binary_root_commutator (hF : 2 < Nat.card F) :
    firstPreimage (binaryProjection (F := F)) =
      Coinvariants.ker ((binaryAction (F := F)).comp (upperUnipotent F).subtype) := by
  change (fixedPlane (F := F)).restrictScalars (ZMod 2) =
    Coinvariants.ker (restrictScalars (action.comp (upperUnipotent F).subtype))
  rw [coinvariants_restrictScalars, root_commutator hF]
lemma binary_root_fixed : firstPreimage (binaryProjection (F := F)) ≤
    fixed ((binaryAction (F := F)).comp (upperUnipotent F).subtype) := by
  intro v hv g
  exact (root_fixed (F := F)).symm.le hv g

/-- All of I.2.3(3) for arbitrary binary covers; their central kernels need not
be subspaces over F. -/
lemma cover_root_geometry (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) (SL F) W}
    (p : σ.IntertwiningMap (binaryNatural (F := F))) (hp : IsCover p) :
    fixed σ ≤ firstPreimage p ∧
      firstPreimage p = Coinvariants.ker (σ.comp (upperUnipotent F).subtype) ∧
      firstPreimage p ≤ fixed (σ.comp (upperUnipotent F).subtype) := by
  have hd : Module.finrank (ZMod 2) (binaryProjection (F := F)).toLinearMap.ker =
      Module.finrank (ZMod 2) (H1 (binaryNatural (F := F)).dual) := by
    rw [binary_kernel_finrank n hF, binary_dual_H1_finrank n hn hF]
  obtain ⟨f,hf,hover⟩ := exists_quotient_of_finrank_ker_eq (k := ZMod 2)
    (ρ := binaryNatural (F := F)) (σ := binaryAction (F := F)) (binaryProjection (F := F))
    (binaryProjection_isCover (card_gt_two n hn hF)) hd p hp
  refine ⟨fixed_le_preimage p (firstLine (F := F)) ?_, ?_⟩
  · rw [natural_fixed]; exact bot_le
  · exact preimage_root_geometry_of_surjective (binaryProjection (F := F)) p f hf hover
      (upperUnipotent F) (firstLine (F := F)) (binary_root_commutator (card_gt_two n hn hF)) (binary_root_fixed (F := F))
end Binary

end Representation.SL2OrthogonalCover
