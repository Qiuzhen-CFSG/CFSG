module

public import Theory.Mathieu.M22.ChapterHLocalClassification.HexadAction.SymplecticComparison.PolarModel
public import Theory.LinearAlgebra.BinaryAlternatingFour
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

/-!
# Faithful binary symplectic representations of the symmetric group on six letters

Normalize the supplied nondegenerate alternating four-form, then conjugate the
faithful representation into the actual matrix group Sp₄(2). Equality of orders
makes this embedding an isomorphism. Comparing it with the concrete polar
isomorphism gives an automorphism of S₆ and an equivariant linear equivalence
with the deleted permutation module. The commutator characterization of A₆
proves compatibility with restriction.

This is the conditional symplectic comparison for Aschbacher–Smith H.14.3(3),
printed p.397. No invariant form is asserted to exist for an arbitrary action.
The explicit normalization is from `Theory.LinearAlgebra.BinaryAlternatingFour`;
the coordinate comparison and its source attribution are in `PolarModel`.
-/

public section

namespace HexadSymplecticComparison
noncomputable section

open Theory.SpecificGroups.SymmetricSix
open Matrix

/-- The binary four-space in the native octad coordinate convention. -/
abbrev V := Fin 4 → ZMod 2

private def shuffle : V ≃ₗ[ZMod 2] NaturalModule where
  toFun v := vec (v 0) (v 2) (v 1) (v 3)
  invFun v := ![v (.inl 0), v (.inr 0), v (.inl 1), v (.inr 1)]
  left_inv v := by ext i; fin_cases i <;> rfl
  right_inv v := by ext i; rcases i with i | i <;> fin_cases i <;> rfl
  map_add' v w := by ext i; rcases i with i | i <;> fin_cases i <;> rfl
  map_smul' c v := by ext i; rcases i with i | i <;> fin_cases i <;> rfl

private theorem shuffle_form (v w : V) :
    polarForm (shuffle v) (shuffle w) = BinaryAlternatingFour.J4.toBilin' v w := by
  decide +revert +kernel

private noncomputable def matrixEquiv (P : BinaryAlternatingFour.Mat) (hP : P.det ≠ 0) :
    V ≃ₗ[ZMod 2] V where
  __ := P.toLin'
  invFun := P⁻¹.mulVec
  left_inv v := by
    change P⁻¹ *ᵥ (P *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hP),
      Matrix.one_mulVec]
  right_inv v := by
    change P *ᵥ (P⁻¹ *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hP),
      Matrix.one_mulVec]

private theorem exists_normalization (B : LinearMap.BilinForm (ZMod 2) V)
    (ha : B.IsAlt) (hn : B.Nondegenerate) :
    ∃ t : V ≃ₗ[ZMod 2] NaturalModule, ∀ v w, polarForm (t v) (t w) = B v w := by
  obtain ⟨P, hP, he⟩ := BinaryAlternatingFour.exists_congruence B.toMatrix'
    (by simpa only [Matrix.toBilin'_toMatrix'] using ha)
    (by simpa only [Matrix.toBilin'_toMatrix'] using hn)
  let e := matrixEquiv P hP
  refine ⟨e.symm.trans shuffle, ?_⟩
  intro v w
  change polarForm (shuffle (e.symm v)) (shuffle (e.symm w)) = B v w
  rw [shuffle_form, ← he, ← Matrix.toBilin'_comp, Matrix.toBilin'_toMatrix']
  change B (e (e.symm v)) (e (e.symm w)) = B v w
  rw [e.apply_symm_apply, e.apply_symm_apply]

/-- Coordinates carrying the supplied form to the exact matrix symplectic convention. -/
noncomputable def normalization (B : LinearMap.BilinForm (ZMod 2) V)
    (ha : B.IsAlt) (hn : B.Nondegenerate) : V ≃ₗ[ZMod 2] NaturalModule :=
  (exists_normalization B ha hn).choose

theorem normalization_form (B : LinearMap.BilinForm (ZMod 2) V)
    (ha : B.IsAlt) (hn : B.Nondegenerate) (v w : V) :
    polarForm (normalization B ha hn v) (normalization B ha hn w) = B v w :=
  (exists_normalization B ha hn).choose_spec v w

variable (rho : S6 →* (V ≃ₗ[ZMod 2] V))
    (B : LinearMap.BilinForm (ZMod 2) V) (ha : B.IsAlt) (hn : B.Nondegenerate)
    (hp : ∀ s v w, B (rho s v) (rho s w) = B v w)

private noncomputable def normalizedMap (s : S6) : NaturalModule →ₗ[ZMod 2] NaturalModule :=
  (normalization B ha hn).toLinearMap ∘ₗ (rho s).toLinearMap ∘ₗ
    (normalization B ha hn).symm.toLinearMap

include hp in
private theorem normalizedMap_preserves (s : S6) (v w : NaturalModule) :
    polarForm (normalizedMap rho B ha hn s v) (normalizedMap rho B ha hn s w) =
      polarForm v w := by
  change polarForm (normalization B ha hn (rho s ((normalization B ha hn).symm v)))
    (normalization B ha hn (rho s ((normalization B ha hn).symm w))) = _
  rw [normalization_form, hp, ← normalization_form B ha hn,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- The representation conjugated into the genuine matrix symplectic group. -/
noncomputable def symplecticHom : S6 →* Matrix.symplecticGroup (Fin 2) (ZMod 2) where
  toFun s := ⟨(normalizedMap rho B ha hn s).toMatrix', by
    rw [SymplecticGroup.mem_iff']
    have hf : polarForm.comp (normalizedMap rho B ha hn s)
        (normalizedMap rho B ha hn s) = polarForm := by
      apply LinearMap.ext
      intro v
      apply LinearMap.ext
      intro w
      exact normalizedMap_preserves rho B ha hn hp s v w
    have hm := congrArg LinearMap.BilinForm.toMatrix' hf
    rw [LinearMap.BilinForm.toMatrix'_comp] at hm
    simpa only [polarForm, LinearMap.BilinForm.toMatrix'_toBilin'] using hm⟩
  map_one' := by
    apply Subtype.ext
    change (normalizedMap rho B ha hn 1).toMatrix' = 1
    rw [← LinearMap.toMatrix'_one]
    congr 1
    ext v
    simp [normalizedMap]
  map_mul' s t := by
    apply Subtype.ext
    change (normalizedMap rho B ha hn (s * t)).toMatrix' =
      (normalizedMap rho B ha hn s).toMatrix' * (normalizedMap rho B ha hn t).toMatrix'
    rw [← LinearMap.toMatrix'_mul]
    congr 1
    ext v
    simp [normalizedMap]

theorem symplecticHom_action (s : S6) (v : V) :
    (symplecticHom rho B ha hn hp s).val *ᵥ normalization B ha hn v =
      normalization B ha hn (rho s v) := by
  change (normalizedMap rho B ha hn s).toMatrix' *ᵥ _ = _
  rw [LinearMap.toMatrix'_mulVec]
  simp [normalizedMap]

theorem symplecticHom_injective (hr : Function.Injective rho) :
    Function.Injective (symplecticHom rho B ha hn hp) := by
  intro s t h
  apply hr
  apply LinearEquiv.ext
  intro v
  apply (normalization B ha hn).injective
  rw [← symplecticHom_action rho B ha hn hp, ← symplecticHom_action rho B ha hn hp, h]

/-- Faithfulness and the order 720 identify the full symplectic group. -/
noncomputable def symplecticEquiv (hr : Function.Injective rho) :
    S6 ≃* Matrix.symplecticGroup (Fin 2) (ZMod 2) :=
  MulEquiv.ofBijective (symplecticHom rho B ha hn hp)
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨symplecticHom_injective rho B ha hn hp hr,
        Nat.card_congr HexadSymplecticComparison.PolarModel.sixToSymplectic.toEquiv⟩)

theorem symplecticEquiv_action (hr : Function.Injective rho) (s : S6) (v : V) :
    (symplecticEquiv rho B ha hn hp hr s).val *ᵥ normalization B ha hn v =
      normalization B ha hn (rho s v) :=
  symplecticHom_action rho B ha hn hp s v

/-- The change of S₆ marking obtained by comparing the two symplectic isomorphisms. -/
noncomputable def automorphism (hr : Function.Injective rho) : S6 ≃* S6 :=
  (symplecticEquiv rho B ha hn hp hr).trans
    HexadSymplecticComparison.PolarModel.sixToSymplectic.symm

/-- The normalized four-space in the actual deleted six-letter permutation module. -/
noncomputable def naturalEquiv : V ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6) :=
  (normalization B ha hn).trans HexadSymplecticComparison.PolarModel.deletedToPolar.symm

theorem naturalEquiv_action (hr : Function.Injective rho) (s : S6) (v : V) :
    naturalEquiv B ha hn (rho s v) = BinaryPermutation.naturalRepresentation (Fin 6)
      (automorphism rho B ha hn hp hr s) (naturalEquiv B ha hn v) := by
  apply HexadSymplecticComparison.PolarModel.deletedToPolar.injective
  rw [HexadSymplecticComparison.PolarModel.deletedToPolar_equivariant]
  have hc (w : V) : HexadSymplecticComparison.PolarModel.deletedToPolar
      (naturalEquiv B ha hn w) = normalization B ha hn w :=
    HexadSymplecticComparison.PolarModel.deletedToPolar.apply_symm_apply _
  rw [hc, hc]
  have hg : polarRepresentation (automorphism rho B ha hn hp hr s) =
      symplecticHom rho B ha hn hp s :=
    HexadSymplecticComparison.PolarModel.sixToSymplectic.apply_symm_apply _
  rw [hg, symplecticHom_action]

theorem automorphism_map_alternating (alpha : S6 ≃* S6) :
    (alternatingGroup (Fin 6)).map alpha.toMonoidHom = alternatingGroup (Fin 6) := by
  rw [← alternatingGroup.commutator_perm_eq (by norm_num : 5 ≤ Nat.card (Fin 6)),
    map_commutator_eq, MonoidHom.range_eq_top.mpr alpha.surjective, commutator_def]

theorem automorphism_mem_alternating (alpha : S6 ≃* S6) {s : S6}
    (hs : s ∈ alternatingGroup (Fin 6)) : alpha s ∈ alternatingGroup (Fin 6) := by
  rw [← automorphism_map_alternating alpha]
  exact ⟨s, hs, rfl⟩

/-- Restriction of any S₆ automorphism to its characteristic alternating subgroup. -/
@[expose] noncomputable def alternatingAutomorphism (alpha : S6 ≃* S6) :
    alternatingGroup (Fin 6) ≃* alternatingGroup (Fin 6) where
  toFun s := ⟨alpha s.val, automorphism_mem_alternating alpha s.property⟩
  invFun s := ⟨alpha.symm s.val, automorphism_mem_alternating alpha.symm s.property⟩
  left_inv s := Subtype.ext (alpha.symm_apply_apply s.val)
  right_inv s := Subtype.ext (alpha.apply_symm_apply s.val)
  map_mul' s t := Subtype.ext (alpha.map_mul s.val t.val)

@[simp] theorem alternatingAutomorphism_coe (alpha : S6 ≃* S6)
    (s : alternatingGroup (Fin 6)) :
    (alternatingAutomorphism alpha s).val = alpha s.val := rfl

theorem naturalEquiv_alternating (hr : Function.Injective rho)
    (s : alternatingGroup (Fin 6)) (v : V) :
    naturalEquiv B ha hn (rho s.val v) = BinaryPermutation.naturalRepresentation (Fin 6)
      (alternatingAutomorphism (automorphism rho B ha hn hp hr) s).val
        (naturalEquiv B ha hn v) :=
  naturalEquiv_action rho B ha hn hp hr s.val v

include B ha hn hp in
/-- The faithful symplectic four-space is the deleted six-letter module after
an explicitly constructed automorphism of the acting group. -/
theorem exists_natural_comparison (hr : Function.Injective rho) :
    ∃ (alpha : S6 ≃* S6) (e : V ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6)),
      (∀ s v, e (rho s v) = BinaryPermutation.naturalRepresentation (Fin 6) (alpha s) (e v)) ∧
      (alternatingGroup (Fin 6)).map alpha.toMonoidHom = alternatingGroup (Fin 6) := by
  exact ⟨automorphism rho B ha hn hp hr, naturalEquiv B ha hn,
    naturalEquiv_action rho B ha hn hp hr, automorphism_map_alternating _⟩

end
end HexadSymplecticComparison
