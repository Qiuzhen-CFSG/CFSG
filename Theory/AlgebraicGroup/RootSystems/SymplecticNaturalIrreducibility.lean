module

public import Theory.AlgebraicGroup.RootSystems.SymplecticRootSubgroups
public import Theory.AlgebraicGroup.Representations.Algebraic.Natural
public import Theory.AlgebraicGroup.Representations.Algebraic.Irreducible

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Irreducibility of the natural symplectic representation

The natural representation of the explicit standard symplectic carrier is
rational by construction.  Its irreducibility is proved directly from the
displayed long and short root matrices: a nonzero invariant submodule first
detects one nonzero coordinate by a long-root transvection, and the short-root
transvections then transport the resulting standard basis vector through both
halves of the symplectic basis.  No ambient root-generation or classification
theorem is used.
-/

universe u

namespace Theory.AlgebraicGroup

open StandardRootSystem

variable {k : Type u} [Field k] [IsAlgClosed k]

public noncomputable def symplecticNaturalRepresentation (m : ℕ) :
    RationalRepresentation
      (standardSymplecticClosedSubgroup (k := k) m).carrierVariety
      (symplecticStandardSpace (k := k) m) :=
  naturalClosedLinearSubgroupRepresentation
    (symplecticStandardBasis (k := k) m)
    (standardSymplecticClosedSubgroup (k := k) m)
    (AlgebraicGroup.Iso.id _)

public theorem symplecticNaturalRepresentation_isRational (m : ℕ) :
    IsRationalRepresentation (symplecticNaturalRepresentation (k := k) m) :=
  naturalClosedLinearSubgroupRepresentation_isRational
    (symplecticStandardBasis (k := k) m)
    (standardSymplecticClosedSubgroup (k := k) m)
    (AlgebraicGroup.Iso.id _)

public theorem symplecticNaturalRepresentation_action (m : ℕ)
    (g : Variety.Point
      (standardSymplecticClosedSubgroup (k := k) m).carrierVariety) :
    (symplecticNaturalRepresentation (k := k) m).action g =
      glPointEquivOf k (symplecticStandardSpace (k := k) m)
        (symplecticStandardBasis (k := k) m)
        ((standardSymplecticClosedSubgroup (k := k) m).inclusion.onPoints g) := by
  rfl

private lemma symplecticNatural_pi_repr_standardSymplecticBasis_symm
    (m : ℕ)
    (c : Fin (Module.finrank k (symplecticStandardSpace (k := k) m)) → k)
    (p : symplecticStandardIndex m) :
    (Pi.basisFun k (symplecticStandardIndex m)).repr
        ((symplecticStandardBasis (k := k) m).equivFun.symm c) p =
      c (symplecticStandardIndexEquiv (k := k) m p) := by
  calc
    (Pi.basisFun k (symplecticStandardIndex m)).repr
        ((symplecticStandardBasis (k := k) m).equivFun.symm c) p =
        (symplecticStandardBasis (k := k) m).equivFun.symm c p := by
          rw [Pi.basisFun_repr]
    _ = (symplecticStandardBasis (k := k) m).repr
        ((symplecticStandardBasis (k := k) m).equivFun.symm c)
          (symplecticStandardIndexEquiv (k := k) m p) :=
      (symplecticStandardBasis_repr_apply (k := k) m _ p).symm
    _ = c (symplecticStandardIndexEquiv (k := k) m p) :=
      congrFun ((symplecticStandardBasis (k := k) m).equivFun.apply_symm_apply c)
        (symplecticStandardIndexEquiv (k := k) m p)

public theorem symplecticNaturalRepresentation_action_matrix (m : ℕ)
    (g : Variety.Point
      (standardSymplecticClosedSubgroup (k := k) m).carrierVariety)
    (x : symplecticStandardSpace (k := k) m) :
    ((symplecticNaturalRepresentation (k := k) m).action g).1 x =
      (symplecticClosedPointMatrix m g).mulVec x := by
  let f := ((symplecticNaturalRepresentation (k := k) m).action g :
    LinearMap.GeneralLinearGroup k (symplecticStandardSpace (k := k) m)).toLinearEquiv
  have hm := LinearMap.toMatrix_mulVec_repr
    (Pi.basisFun k (symplecticStandardIndex m))
    (Pi.basisFun k (symplecticStandardIndex m)) f x
  have hmat : LinearMap.toMatrix (Pi.basisFun k (symplecticStandardIndex m))
      (Pi.basisFun k (symplecticStandardIndex m)) f =
      symplecticClosedPointMatrix m g := by
    ext p q
    rw [LinearMap.toMatrix_apply, symplecticClosedPointMatrix_entry]
    change (Pi.basisFun k (symplecticStandardIndex m)).repr
      ((glPointEquivOf k (symplecticStandardSpace (k := k) m)
        (symplecticStandardBasis (k := k) m)
        ((standardSymplecticClosedSubgroup (k := k) m).inclusion.onPoints g)).1
        ((Pi.basisFun k (symplecticStandardIndex m)) q)) p = _
    rw [Pi.basisFun_apply, ← symplecticStandardBasis_apply (k := k) m q,
      glPointEquivOf_apply_basis]
    rw [symplecticNatural_pi_repr_standardSymplecticBasis_symm]
    change ((standardSymplecticClosedSubgroup (k := k) m).pointEquiv g).val.val
      (Sum.inl ((symplecticStandardIndexEquiv (k := k) m) p,
        (symplecticStandardIndexEquiv (k := k) m) q)) = _
    exact congrArg (fun z => z (Sum.inl ((symplecticStandardIndexEquiv (k := k) m) p,
      (symplecticStandardIndexEquiv (k := k) m) q)))
      ((standardSymplecticClosedSubgroup (k := k) m).pointEquiv_val g)
  rw [hmat] at hm
  have hm' := hm.symm
  have hrx : ((Pi.basisFun k (symplecticStandardIndex m)).repr x :
      symplecticStandardIndex m → k) = x := by
    ext i
    simp [Pi.basisFun_repr]
  have hry : ((Pi.basisFun k (symplecticStandardIndex m)).repr
      ((f : _ →ₗ[k] _) x) : symplecticStandardIndex m → k) = f x := by
    ext i
    simp [Pi.basisFun_repr]
  rw [hrx] at hm'
  change (f x) = _
  rw [hry] at hm'
  simpa [f] using hm'

private lemma symplecticNatural_long_upper_apply (m : ℕ) (i : Fin m) (a : k)
    (x : symplecticStandardSpace (k := k) m) :
    (symplecticRootMatrix (k := k) m (.inr ⟨i, false⟩) a).mulVec x =
      x + (a * x (Sum.inr i)) • Pi.single (Sum.inl i) 1 := by
  ext p
  classical
  cases p with
  | inl p =>
    by_cases h : p = i
    · subst p
      simp [symplecticRootMatrix, symplecticSingle, Matrix.mulVec, dotProduct,
        Matrix.fromBlocks, Matrix.one_apply, Matrix.single_apply, Pi.single_apply]
    · simp [symplecticRootMatrix, symplecticSingle, Matrix.mulVec, dotProduct,
        Matrix.fromBlocks, Matrix.one_apply, Matrix.single_apply, Pi.single_apply,
        h, Ne.symm h, Finset.sum_eq_zero]
  | inr p =>
    simp [symplecticRootMatrix, symplecticSingle, Matrix.mulVec, dotProduct,
      Matrix.fromBlocks, Matrix.one_apply, Matrix.single_apply, Pi.single_apply]

private lemma symplecticNatural_long_lower_apply (m : ℕ) (i : Fin m) (a : k)
    (x : symplecticStandardSpace (k := k) m) :
    (symplecticRootMatrix (k := k) m (.inr ⟨i, true⟩) a).mulVec x =
      x + (a * x (Sum.inl i)) • Pi.single (Sum.inr i) 1 := by
  ext p
  classical
  cases p with
  | inl p =>
    simp [symplecticRootMatrix, symplecticSingle, Matrix.mulVec, dotProduct,
      Matrix.fromBlocks, Matrix.one_apply, Matrix.single_apply, Pi.single_apply]
  | inr p =>
    by_cases h : p = i
    · subst p
      simp [symplecticRootMatrix, symplecticSingle, Matrix.mulVec, dotProduct,
        Matrix.fromBlocks, Matrix.one_apply, Matrix.single_apply, Pi.single_apply]
      ring
    · simp [symplecticRootMatrix, symplecticSingle, Matrix.mulVec, dotProduct,
        Matrix.fromBlocks, Matrix.one_apply, Matrix.single_apply, Pi.single_apply,
        h, Ne.symm h, Finset.sum_eq_zero]

private lemma symplecticNatural_pair_upper_add_lt (m : ℕ) (i j : Fin m)
    (hij : i < j) (a : k) :
    (symplecticRootMatrix (k := k) m
      (.inl ⟨⟨⟨i, j⟩, hij⟩, ⟨-1, by simp⟩, ⟨1, by simp⟩⟩) a).mulVec
      (Pi.single (Sum.inl i) 1) =
      Pi.single (Sum.inl i) 1 + a • Pi.single (Sum.inl j) 1 := by
  rw [Matrix.mulVec_single_one]
  simp only [symplecticRootMatrix]
  norm_num
  ext p
  cases p with
  | inl p =>
    by_cases hpi : p = i
    · subst p
      simp [symplecticSingle, Matrix.fromBlocks, Matrix.single_apply,
        Pi.single_apply, hij.ne]
      intro hji
      exact (hij.ne' hji).elim
    · by_cases hpj : p = j
      · subst p
        simp [symplecticSingle, Matrix.fromBlocks, Matrix.single_apply,
          Pi.single_apply, hij.ne, hij.ne']
      · have hpi' : i ≠ p := Ne.symm hpi
        have hpj' : j ≠ p := Ne.symm hpj
        simp [symplecticSingle, Matrix.fromBlocks, Matrix.single_apply,
          Pi.single_apply, hpi, hpj, hpi', hpj', hij.ne, hij.ne']
  | inr p =>
    simp [symplecticSingle, Matrix.fromBlocks, Matrix.single_apply,
      Pi.single_apply]

private lemma symplecticNatural_pair_upper_add_gt (m : ℕ) (i j : Fin m)
    (hji : j < i) (a : k) :
    (symplecticRootMatrix (k := k) m
      (.inl ⟨⟨⟨j, i⟩, hji⟩, ⟨1, by simp⟩, ⟨-1, by simp⟩⟩) a).mulVec
      (Pi.single (Sum.inl i) 1) =
      Pi.single (Sum.inl i) 1 + a • Pi.single (Sum.inl j) 1 := by
  rw [Matrix.mulVec_single_one]
  simp only [symplecticRootMatrix]
  norm_num
  ext p
  cases p with
  | inl p =>
    by_cases hpi : p = i
    · subst p
      simp [symplecticSingle, Matrix.fromBlocks, Matrix.single_apply,
        Pi.single_apply, hji.ne]
    · by_cases hpj : p = j
      · subst p
        simp [symplecticSingle, Matrix.fromBlocks, Matrix.single_apply,
          Pi.single_apply, hji.ne, hji.ne']
      · have hpi' : i ≠ p := Ne.symm hpi
        have hpj' : j ≠ p := Ne.symm hpj
        simp [symplecticSingle, Matrix.fromBlocks, Matrix.single_apply,
          Pi.single_apply, hpi, hpj, hpi', hpj', hji.ne, hji.ne']
  | inr p =>
    simp [symplecticSingle, Matrix.fromBlocks, Matrix.single_apply,
      Pi.single_apply]

private lemma symplecticNatural_pair_lower_sub_lt (m : ℕ) (i j : Fin m)
    (hij : i < j) (a : k) :
    (symplecticRootMatrix (k := k) m
      (.inl ⟨⟨⟨i, j⟩, hij⟩, ⟨1, by simp⟩, ⟨-1, by simp⟩⟩) a).mulVec
      (Pi.single (Sum.inr i) 1) =
      Pi.single (Sum.inr i) 1 - a • Pi.single (Sum.inr j) 1 := by
  rw [Matrix.mulVec_single_one]
  simp only [symplecticRootMatrix]
  norm_num
  ext p
  cases p with
  | inl p => simp [symplecticSingle, Matrix.fromBlocks, Matrix.single_apply,
      Pi.single_apply]
  | inr p =>
    by_cases hpi : p = i
    · subst p
      simp [symplecticSingle, Matrix.fromBlocks, Matrix.single_apply,
        Pi.single_apply, hij.ne]
      intro hji
      exact (hij.ne' hji).elim
    · by_cases hpj : p = j
      · subst p
        simp [symplecticSingle, Matrix.fromBlocks, Matrix.single_apply,
          Pi.single_apply, hij.ne, hij.ne']
      · have hpi' : i ≠ p := Ne.symm hpi
        have hpj' : j ≠ p := Ne.symm hpj
        simp [symplecticSingle, Matrix.fromBlocks, Matrix.single_apply,
          Pi.single_apply, hpi, hpj, hpi', hpj', hij.ne, hij.ne']

private lemma symplecticNatural_pair_lower_sub_gt (m : ℕ) (i j : Fin m)
    (hji : j < i) (a : k) :
    (symplecticRootMatrix (k := k) m
      (.inl ⟨⟨⟨j, i⟩, hji⟩, ⟨-1, by simp⟩, ⟨1, by simp⟩⟩) a).mulVec
      (Pi.single (Sum.inr i) 1) =
      Pi.single (Sum.inr i) 1 - a • Pi.single (Sum.inr j) 1 := by
  rw [Matrix.mulVec_single_one]
  simp only [symplecticRootMatrix]
  norm_num
  ext p
  cases p with
  | inl p => simp [symplecticSingle, Matrix.fromBlocks, Matrix.single_apply,
      Pi.single_apply]
  | inr p =>
    by_cases hpi : p = i
    · subst p
      simp [symplecticSingle, Matrix.fromBlocks, Matrix.single_apply,
        Pi.single_apply, hji.ne]
    · by_cases hpj : p = j
      · subst p
        simp [symplecticSingle, Matrix.fromBlocks, Matrix.single_apply,
          Pi.single_apply, hji.ne, hji.ne']
      · have hpi' : i ≠ p := Ne.symm hpi
        have hpj' : j ≠ p := Ne.symm hpj
        simp [symplecticSingle, Matrix.fromBlocks, Matrix.single_apply,
          Pi.single_apply, hpi, hpj, hpi', hpj', hji.ne, hji.ne']

private lemma symplecticNatural_long_transfer_upper_lower
    (m : ℕ) (i : Fin m) (W : Submodule k (symplecticStandardSpace (k := k) m))
    (hW : IsInvariantSubmodule (symplecticNaturalRepresentation (k := k) m) W)
    (hi : Pi.single (Sum.inl i) 1 ∈ W) :
    Pi.single (Sum.inr i) 1 ∈ W := by
  have h := hW (symplecticRootPoint (k := k) m (.inr ⟨i, true⟩) 1)
      (Pi.single (Sum.inl i) 1) hi
  rw [symplecticNaturalRepresentation_action_matrix,
    symplecticClosedPointMatrix_rootPoint, symplecticNatural_long_lower_apply] at h
  have hd := W.sub_mem h hi
  simpa using hd

private lemma symplecticNatural_long_transfer_lower_upper
    (m : ℕ) (i : Fin m) (W : Submodule k (symplecticStandardSpace (k := k) m))
    (hW : IsInvariantSubmodule (symplecticNaturalRepresentation (k := k) m) W)
    (hi : Pi.single (Sum.inr i) 1 ∈ W) :
    Pi.single (Sum.inl i) 1 ∈ W := by
  have h := hW (symplecticRootPoint (k := k) m (.inr ⟨i, false⟩) 1)
      (Pi.single (Sum.inr i) 1) hi
  rw [symplecticNaturalRepresentation_action_matrix,
    symplecticClosedPointMatrix_rootPoint, symplecticNatural_long_upper_apply] at h
  have hd := W.sub_mem h hi
  simpa using hd

private lemma symplecticNatural_upper_propagate
    (m : ℕ) (i : Fin m) (W : Submodule k (symplecticStandardSpace (k := k) m))
    (hW : IsInvariantSubmodule (symplecticNaturalRepresentation (k := k) m) W)
    (hi : Pi.single (Sum.inl i) 1 ∈ W) (j : Fin m) :
    Pi.single (Sum.inl j) 1 ∈ W := by
  by_cases hij : i = j
  · simpa [hij] using hi
  · rcases lt_or_gt_of_ne hij with hlt | hgt
    · have h := hW (symplecticRootPoint (k := k) m
          (.inl ⟨⟨⟨i, j⟩, hlt⟩, ⟨-1, by simp⟩, ⟨1, by simp⟩⟩) 1)
          (Pi.single (Sum.inl i) 1) hi
      rw [symplecticNaturalRepresentation_action_matrix,
        symplecticClosedPointMatrix_rootPoint,
        symplecticNatural_pair_upper_add_lt] at h
      have hd := W.sub_mem h hi
      simpa using hd
    · have h := hW (symplecticRootPoint (k := k) m
          (.inl ⟨⟨⟨j, i⟩, hgt⟩, ⟨1, by simp⟩, ⟨-1, by simp⟩⟩) 1)
          (Pi.single (Sum.inl i) 1) hi
      rw [symplecticNaturalRepresentation_action_matrix,
        symplecticClosedPointMatrix_rootPoint,
        symplecticNatural_pair_upper_add_gt] at h
      have hd := W.sub_mem h hi
      simpa using hd

private lemma symplecticNatural_lower_propagate
    (m : ℕ) (i : Fin m) (W : Submodule k (symplecticStandardSpace (k := k) m))
    (hW : IsInvariantSubmodule (symplecticNaturalRepresentation (k := k) m) W)
    (hi : Pi.single (Sum.inr i) 1 ∈ W) (j : Fin m) :
    Pi.single (Sum.inr j) 1 ∈ W := by
  by_cases hij : i = j
  · simpa [hij] using hi
  · rcases lt_or_gt_of_ne hij with hlt | hgt
    · have h := hW (symplecticRootPoint (k := k) m
          (.inl ⟨⟨⟨i, j⟩, hlt⟩, ⟨1, by simp⟩, ⟨-1, by simp⟩⟩) 1)
          (Pi.single (Sum.inr i) 1) hi
      rw [symplecticNaturalRepresentation_action_matrix,
        symplecticClosedPointMatrix_rootPoint,
        symplecticNatural_pair_lower_sub_lt] at h
      have hd := W.sub_mem h hi
      have hn := W.neg_mem hd
      simpa using hn
    · have h := hW (symplecticRootPoint (k := k) m
          (.inl ⟨⟨⟨j, i⟩, hgt⟩, ⟨-1, by simp⟩, ⟨1, by simp⟩⟩) 1)
          (Pi.single (Sum.inr i) 1) hi
      rw [symplecticNaturalRepresentation_action_matrix,
        symplecticClosedPointMatrix_rootPoint,
        symplecticNatural_pair_lower_sub_gt] at h
      have hd := W.sub_mem h hi
      have hn := W.neg_mem hd
      simpa using hn

public theorem symplecticNaturalRepresentation_isAlgebraicallyIrreducible
    (m : ℕ) (hm : 0 < m) :
    IsAlgebraicallyIrreducibleRepresentation
      (symplecticNaturalRepresentation (k := k) m) := by
  intro W hW
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  · right
    have hWne : ∃ x : symplecticStandardSpace (k := k) m, x ∈ W ∧ x ≠ 0 := by
      by_contra h
      push Not at h
      apply hbot
      apply bot_unique
      intro x hx
      exact h x hx
    obtain ⟨x, hxW, hx0⟩ := hWne
    have hcoord : ∃ s : symplecticStandardIndex m, x s ≠ 0 := by
      by_contra h
      push Not at h
      exact hx0 (funext h)
    obtain ⟨s, hs⟩ := hcoord
    have hbase : ∃ i : Fin m, Pi.single (Sum.inl i) 1 ∈ W := by
      cases s with
      | inl i =>
        have h := hW (symplecticRootPoint (k := k) m (.inr ⟨i, true⟩)
            (x (Sum.inl i))⁻¹) x hxW
        rw [symplecticNaturalRepresentation_action_matrix,
          symplecticClosedPointMatrix_rootPoint,
          symplecticNatural_long_lower_apply] at h
        have hd := W.sub_mem h hxW
        refine ⟨i, ?_⟩
        apply symplecticNatural_long_transfer_lower_upper m i W hW
        simpa [hs, inv_mul_cancel₀ hs] using hd
      | inr i =>
        have h := hW (symplecticRootPoint (k := k) m (.inr ⟨i, false⟩)
            (x (Sum.inr i))⁻¹) x hxW
        rw [symplecticNaturalRepresentation_action_matrix,
          symplecticClosedPointMatrix_rootPoint,
          symplecticNatural_long_upper_apply] at h
        have hd := W.sub_mem h hxW
        refine ⟨i, ?_⟩
        simpa [hs, inv_mul_cancel₀ hs] using hd
    obtain ⟨i, hi⟩ := hbase
    have hallUpper : ∀ j : Fin m, Pi.single (Sum.inl j) 1 ∈ W :=
      symplecticNatural_upper_propagate m i W hW hi
    have hiLower := symplecticNatural_long_transfer_upper_lower m i W hW hi
    have hallLower : ∀ j : Fin m, Pi.single (Sum.inr j) 1 ∈ W :=
      symplecticNatural_lower_propagate m i W hW hiLower
    apply (Submodule.eq_top_iff_forall_basis_mem
      (symplecticStandardBasis (k := k) m)).2
    intro q
    let s := (symplecticStandardIndexEquiv (k := k) m).symm q
    rw [show q = symplecticStandardIndexEquiv (k := k) m s by
      exact (symplecticStandardIndexEquiv (k := k) m).apply_symm_apply q |>.symm,
      symplecticStandardBasis_apply]
    cases s with
    | inl i => exact hallUpper i
    | inr i => exact hallLower i

end Theory.AlgebraicGroup
