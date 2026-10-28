module

public import Theory.Representation.BinaryPermutation.FiveGeometry

/-!
# Recovering permutations from the five singular vectors

The nonzero singular vectors of the five-point core are the five words with
one zero coordinate. They span the core: a core word is the sum of these
five vectors with its own coordinates as coefficients. Thus a linear
isometry permutes the five singular vectors and is exactly the corresponding
coordinate permutation on every vector. This also proves faithfulness of
the permutation action.

The finite identities range over at most 32 words; the isometry argument is
structural and does not enumerate linear maps or groups. These facts supply
the action comparison in Aschbacher–Smith, K.3.1.2, printed p.454, with the
permutation-module conventions of B.3, pp.83–84.
-/

@[expose] public noncomputable section
namespace Representation.OrthogonalFourMinus.FivePoint.Construction
open BinaryPermutation

private def pointWord (i : Fin 5) : Full (Fin 5) := fun j => if j = i then 0 else 1

private theorem point_mem : ∀ i, pointWord i ∈ core (Fin 5) := by
  change ∀ i, ∑ j, pointWord i j = 0
  decide

private def point (i : Fin 5) : core (Fin 5) := ⟨pointWord i, point_mem i⟩

private theorem point_injective : Function.Injective point := by
  have h : ∀ i j : Fin 5, pointWord i = pointWord j → i = j := by decide
  intro i j hij
  exact h i j (congrArg Subtype.val hij)

private theorem point_singular (i : Fin 5) : point i ≠ 0 ∧ FiveGeometry.form (point i) = 0 := by
  have h : ∀ i : Fin 5, pointWord i ≠ 0 ∧
      (∑ j : Fin 5, ∑ k : Fin 5 with j < k, pointWord i j * pointWord i k) = 0 := by decide
  exact ⟨fun he => (h i).1 (congrArg Subtype.val he), (h i).2⟩

private theorem singular_point (w : core (Fin 5)) (hw : w ≠ 0) (hq : FiveGeometry.form w = 0) :
    ∃ i, point i = w := by
  have h : ∀ w : Full (Fin 5), (∑ i, w i) = 0 → w ≠ 0 →
      (∑ i : Fin 5, ∑ j : Fin 5 with i < j, w i * w j) = 0 →
      ∃ i, pointWord i = w := by decide
  obtain ⟨i, hi⟩ := h w.val w.property (fun he => hw (Subtype.ext he)) hq
  exact ⟨i, Subtype.ext hi⟩

private theorem point_decomposition (w : core (Fin 5)) :
    w = ∑ i, w.val i • point i := by
  have h : ∀ w : Full (Fin 5), (∑ i, w i) = 0 → w = ∑ i, w i • pointWord i := by decide
  apply Subtype.ext
  simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower, point] using h w.val w.property

private theorem permute_point (p : Equiv.Perm (Fin 5)) (i : Fin 5) :
    coreRepresentation (Fin 5) p (point i) = point (p i) := by
  apply Subtype.ext
  funext j
  change (if p.symm j = i then (0 : ZMod 2) else 1) =
    (if j = p i then 0 else 1)
  simp only [Equiv.symm_apply_eq]

private abbrev Singular := {w : core (Fin 5) // w ≠ 0 ∧ FiveGeometry.form w = 0}

private def pointsEquiv : Fin 5 ≃ Singular :=
  Equiv.ofBijective (fun i => ⟨point i, point_singular i⟩) ⟨by
    intro i j h
    exact point_injective (congrArg Subtype.val h), by
    rintro ⟨w, hw, hq⟩
    obtain ⟨i, hi⟩ := singular_point w hw hq
    exact ⟨i, Subtype.ext hi⟩⟩

private def singularEquiv (e : core (Fin 5) ≃ₗ[ZMod 2] core (Fin 5))
    (hq : ∀ w, FiveGeometry.form (e w) = FiveGeometry.form w) : Singular ≃ Singular where
  toFun w := ⟨e w, by simpa only [ne_eq, EmbeddingLike.map_eq_zero_iff, hq] using w.property⟩
  invFun w := ⟨e.symm w, by
    constructor
    · intro hz
      exact w.property.1 (by simpa only [LinearEquiv.apply_symm_apply, map_zero] using congrArg e hz)
    · rw [← hq, LinearEquiv.apply_symm_apply]
      exact w.property.2⟩
  left_inv w := Subtype.ext (e.symm_apply_apply w)
  right_inv w := Subtype.ext (e.apply_symm_apply w)

/-- Every linear isometry of the five-point quadratic core is its coordinate
permutation on the five nonzero singular vectors. -/
theorem exists_permutation_of_isometry (e : core (Fin 5) ≃ₗ[ZMod 2] core (Fin 5))
    (hq : ∀ w, FiveGeometry.form (e w) = FiveGeometry.form w) :
    ∃ p : Equiv.Perm (Fin 5), ∀ w, e w = coreRepresentation (Fin 5) p w := by
  let p := pointsEquiv.trans ((singularEquiv e hq).trans pointsEquiv.symm)
  have hp (i : Fin 5) : point (p i) = e (point i) := by
    exact congrArg Subtype.val (pointsEquiv.apply_symm_apply (singularEquiv e hq (pointsEquiv i)))
  refine ⟨p, fun w => ?_⟩
  rw [point_decomposition w, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, map_smul, permute_point, hp]

/-- The coordinate permutation is determined by its linear action on the core. -/
theorem core_permutation_injective : Function.Injective (coreRepresentation (Fin 5)) := by
  intro p q h
  apply Equiv.ext
  intro i
  apply point_injective
  rw [← permute_point, ← permute_point]
  exact LinearMap.congr_fun h (point i)

end Representation.OrthogonalFourMinus.FivePoint.Construction
