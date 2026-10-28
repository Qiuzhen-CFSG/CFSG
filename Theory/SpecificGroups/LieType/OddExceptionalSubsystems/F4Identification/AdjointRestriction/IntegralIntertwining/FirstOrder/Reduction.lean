module
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.AdjointRestriction.IntegralIntertwining.Operators
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.AdjointRestriction.IntegralIntertwining.FirstOrder.RowFormulas

/-!
# Reduction of the first-order E6--F4 comparison to root geometry

The integral fibre-incidence matrix respects the Geck sign involutions, so
positive comparisons imply the negative comparisons. On positive Cartan rows
the comparison follows from the prescribed simple-root projection. On root
rows the Cartan columns use the simple fibres and the explicit Cartan table;
the root columns use the sum of bottom string lengths over a node fibre.
All sums and coefficients belong to the actual E6 and F4 root pairings.

`firstOrder_intertwines_of_root_geometry` and its literal integral-column
application retain three geometric hypotheses: projection of every E6 root
is an F4 root, the fibres over simple F4 roots consist of the indicated E6
simple roots, and bottom string lengths add over each node fibre. This module
does not claim those hypotheses or the unconditional first-order comparison.
The final assembly belongs to `FirstOrder`.

The row calculation uses root-string recurrence, not a matrix certificate.
Only the 24 scalar Cartan entries are checked by kernel reduction.

Sources: integral Geck operators; GLS3 §§2.2--2.6;
Aschbacher--Smith A.2.17, printed p.39 of `refs/quasithin.pdf`.
-/

public section
noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem Matrix
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
attribute [local instance] Classical.decEq
namespace TwistedE6.FoldedSubsystem.F4Identification.AdjointRestriction
local instance : Fintype typeF4Roots := Fintype.ofFinite _

private theorem e6_neg_val (r : typeE6Roots) :
    (typeE6RootPairing.reflectionPerm r r).val = -r.val := by
  have h := typeE6RootPairing.root_reflectionPerm r r
  rw [RootPairing.reflection_apply_self] at h
  exact congrArg Subtype.val h

private theorem f4_neg_val (r : typeF4Roots) :
    (typeF4RootPairing.reflectionPerm r r).val = -r.val := by
  have h := typeF4RootPairing.root_reflectionPerm r r
  rw [RootPairing.reflection_apply_self] at h
  simpa only [typeF4RootPairing_root, typeF4RootEmbedding_apply] using h

/-- The integral orbit-sum map respects the sign involution. -/
theorem omegaMatrix_intertwines :
    omegaMatrix (b := TwistedE6.Base) * latticeMatrix =
      latticeMatrix * omegaMatrix (b := typeF4RootPairing_base) := by
  ext (i | r) (j | a)
  · rw [omega_mul_inl, mul_omega_inl]
  · rw [omega_mul_inl, mul_omega_inr]
    rfl
  · rw [omega_mul_inr, mul_omega_inl]
    rfl
  · rw [omega_mul_inr, mul_omega_inr]
    simp only [latticeMatrix, e6_neg_val, f4_neg_val, map_neg, neg_eq_iff_eq_neg]

private theorem matrix_int : matrix ℤ = latticeMatrix := by
  ext i j
  simp [matrix]

private theorem lattice_mul_cartan (A : Matrix SourceIndex SourceIndex ℤ)
    (k : Fin 6) (c : SourceIndex) :
    (latticeMatrix * A) (.inl (simpleIndex k)) c = A (.inl (sourceIndex (node k))) c := by
  have h := linearMap_cartan ℤ (fun d => A d c) k
  simpa only [linearMap, matrix_int, Matrix.mulVecLin_apply, Matrix.mul_apply,
    Matrix.mulVec, dotProduct] using h

private theorem lattice_mul_root (A : Matrix SourceIndex SourceIndex ℤ)
    (r : typeE6Roots) (a : typeF4Roots) (h : rootProjection r.val = a.val) (c : SourceIndex) :
    (latticeMatrix * A) (.inr r) c = A (.inr a) c := by
  have hh := linearMap_root ℤ (fun d => A d c) r a h
  simpa only [linearMap, matrix_int, Matrix.mulVecLin_apply, Matrix.mul_apply,
    Matrix.mulVec, dotProduct] using hh

/-- The folding is the sum on each numbered node fibre. -/
theorem foldedOperator_eq_sum (s : Bool) (i : Fin 4) :
    foldedOperator s i = ∑ j : Fin 6, if node j = i then targetOperator s j else 0 := by
  fin_cases i <;> simp [foldedOperator, node, Fin.sum_univ_succ]

private theorem folded_mul_lattice (s : Bool) (i : Fin 4)
    (r : TwistedE6.Index) (c : SourceIndex) :
    (foldedOperator s i * latticeMatrix) r c =
      ∑ j : Fin 6, if node j = i then (targetOperator s j * latticeMatrix) r c else 0 := by
  rw [foldedOperator_eq_sum, Matrix.sum_mul, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

attribute [-instance] Classical.decEq in
/-- Absolute Cartan coefficients fold with the source's actual numbering. -/
theorem folded_cartan_abs (j : Fin 6) (l : Fin 4) :
    (∑ k : Fin 6, |typeE6CartanMatrix j k| * (if node k = l then 1 else 0)) =
      |typeF4CartanMatrix (node j) l| := by
  decide +kernel +revert

private theorem target_mul_lattice_root_root (j : Fin 6) (r : typeE6Roots)
    (a : typeF4Roots) :
    (targetOperator true j * latticeMatrix) (.inr r) (.inr a) =
      if rootProjection r.val = typeF4SimpleRoot (node j) + a.val then
        (typeE6RootPairing.chainBotCoeff (simpleIndex j) r : ℤ) else 0 := by
  change (eMatrix (simpleIndex j) * latticeMatrix) (.inr r) (.inr a) = _
  rw [eMatrix_mul_root_row]
  simp only [latticeMatrix, mul_zero, Finset.sum_const_zero, ite_self, zero_add]
  have h := eMatrix_root_row_project (simpleIndex j) r
    (rootProjection.comp typeE6RootSpan.subtype) a.val
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, typeE6RootPairing_root,
    typeE6RootInSpan_val, typeE6RootPairing_baseEquiv_val, typeE6SimpleRootIndex_val,
    rootProjection_simple] at h
  refine Eq.trans ?_ (Eq.trans h ?_)
  · apply Finset.sum_congr rfl
    intro t _
    congr 1
    exact (ite_eq_ite _ _ _).mpr trivial
  · exact (ite_eq_ite _ _ _).mpr trivial

private theorem lattice_source_root_root (i : Fin 4) (r : typeE6Roots)
    (a b : typeF4Roots) (h : rootProjection r.val = b.val) :
    (latticeMatrix * sourceOperator true i) (.inr r) (.inr a) =
      if rootProjection r.val = typeF4SimpleRoot i + a.val then
        (typeF4RootPairing.chainBotCoeff (sourceIndex i) b : ℤ) else 0 := by
  rw [lattice_mul_root _ r b h]
  change eMatrix (sourceIndex i) (.inr b) (.inr a) = _
  simp only [eMatrix_root_row, typeF4RootPairing_root,
    typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, h]
  exact (ite_eq_ite _ _ _).mpr trivial

private theorem target_mul_lattice_root_cartan (j : Fin 6) (r : typeE6Roots)
    (l : Fin 4) :
    (targetOperator true j * latticeMatrix) (.inr r) (.inl (sourceIndex l)) =
      if r = typeE6SimpleRootIndex j then |typeF4CartanMatrix (node j) l| else 0 := by
  change (eMatrix (simpleIndex j) * latticeMatrix) (.inr r) (.inl (sourceIndex l)) = _
  rw [eMatrix_mul_root_row]
  simp only [latticeMatrix, mul_zero, Finset.sum_const_zero, add_zero]
  rw [← typeE6RootPairing_baseEquiv.sum_comp]
  simp only [simpleIndex, sourceIndex, Equiv.symm_apply_apply, Equiv.apply_eq_iff_eq,
    typeE6RootPairing_base_cartan_apply, typeE6RootPairing_baseEquiv_val, folded_cartan_abs]

private theorem target_mul_lattice_cartan (j k : Fin 6) (c : SourceIndex) :
    (targetOperator true j * latticeMatrix) (.inl (simpleIndex k)) c =
      if k = j then
        latticeMatrix (.inr (typeE6RootPairing.reflectionPerm (simpleIndex j) (simpleIndex j))) c
      else 0 := by
  change (eMatrix (simpleIndex j) * latticeMatrix) (.inl (simpleIndex k)) c = _
  rw [eMatrix_mul_cartan_row]
  simp only [simpleIndex, Equiv.apply_eq_iff_eq]

private theorem firstOrder_cartan_row (i : Fin 4) (k : Fin 6) (c : SourceIndex) :
    (foldedOperator true i * latticeMatrix) (.inl (simpleIndex k)) c =
      (latticeMatrix * sourceOperator true i) (.inl (simpleIndex k)) c := by
  rw [folded_mul_lattice, lattice_mul_cartan]
  simp_rw [target_mul_lattice_cartan]
  rw [Finset.sum_eq_single k]
  · simp only [if_true]
    rcases c with l | a
    · simp only [latticeMatrix, ite_self]
      rfl
    · by_cases hn : node k = i
      · have ha :
            rootProjection (typeE6RootPairing.reflectionPerm (simpleIndex k) (simpleIndex k)).val = a.val ↔
            a = typeF4RootPairing.reflectionPerm (sourceIndex i) (sourceIndex i) := by
          rw [e6_neg_val, map_neg]
          change -rootProjection (typeE6SimpleRoot k) = a.val ↔ _
          rw [rootProjection_simple, hn, Subtype.ext_iff, f4_neg_val]
          exact eq_comm
        simp only [hn, if_true, latticeMatrix, ha]
        change _ = if sourceIndex i = sourceIndex i ∧
          a = typeF4RootPairing.reflectionPerm (sourceIndex i) (sourceIndex i) then 1 else 0
        simp only [true_and]
      · have hs : sourceIndex (node k) ≠ sourceIndex i := fun h =>
          hn (typeF4RootPairing_baseEquiv.injective h)
        simp only [hn, if_false]
        change 0 = if sourceIndex (node k) = sourceIndex i ∧
          a = typeF4RootPairing.reflectionPerm (sourceIndex i) (sourceIndex i) then 1 else 0
        simp only [hs, false_and, if_false]
  · intro j _ hj
    simp only [Ne.symm hj, if_false, ite_self]
  · simp

private theorem firstOrder_root_root
    (hroot : ∀ r : typeE6Roots, rootProjection r.val ∈ typeF4Roots)
    (hchain : ∀ (i : Fin 4) (r : typeE6Roots) (a : typeF4Roots),
      rootProjection r.val = a.val →
        (∑ j : Fin 6, if node j = i then
          typeE6RootPairing.chainBotCoeff (simpleIndex j) r else 0) =
          typeF4RootPairing.chainBotCoeff (sourceIndex i) a)
    (i : Fin 4) (r : typeE6Roots) (a : typeF4Roots) :
    (foldedOperator true i * latticeMatrix) (.inr r) (.inr a) =
      (latticeMatrix * sourceOperator true i) (.inr r) (.inr a) := by
  let b : typeF4Roots := ⟨rootProjection r.val, hroot r⟩
  have hb : rootProjection r.val = b.val := rfl
  have hc : (∑ j : Fin 6, if node j = i then
      (typeE6RootPairing.chainBotCoeff (simpleIndex j) r : ℤ) else 0) =
      (typeF4RootPairing.chainBotCoeff (sourceIndex i) b : ℤ) := by
    exact_mod_cast hchain i r b hb
  rw [folded_mul_lattice, lattice_source_root_root i r a b hb]
  simp_rw [target_mul_lattice_root_root]
  by_cases h : rootProjection r.val = typeF4SimpleRoot i + a.val
  · simp only [if_pos h]
    rw [← hc]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : node j = i <;> simp [hj, h]
  · simp only [if_neg h]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : node j = i <;> simp [hj, h]

private theorem firstOrder_root_cartan
    (hroot : ∀ r : typeE6Roots, rootProjection r.val ∈ typeF4Roots)
    (hsimple : ∀ (i : Fin 4) (r : typeE6Roots),
      rootProjection r.val = typeF4SimpleRoot i →
        ∃ j : Fin 6, node j = i ∧ r = typeE6SimpleRootIndex j)
    (i : Fin 4) (r : typeE6Roots) (l : Fin 4) :
    (foldedOperator true i * latticeMatrix) (.inr r) (.inl (sourceIndex l)) =
      (latticeMatrix * sourceOperator true i) (.inr r) (.inl (sourceIndex l)) := by
  let b : typeF4Roots := ⟨rootProjection r.val, hroot r⟩
  have hb : rootProjection r.val = b.val := rfl
  have hs : sourceOperator true i (.inr b) (.inl (sourceIndex l)) =
      if rootProjection r.val = typeF4SimpleRoot i then |typeF4CartanMatrix i l| else 0 := by
    change (if b = (sourceIndex i : typeF4Roots) then
      |typeF4RootPairing_base.cartanMatrix (sourceIndex i) (sourceIndex l)| else 0) = _
    rw [typeF4RootPairing_base_cartan_apply]
    have he : b = (sourceIndex i : typeF4Roots) ↔ rootProjection r.val = typeF4SimpleRoot i :=
      Subtype.ext_iff
    simp only [he]
  rw [folded_mul_lattice, lattice_mul_root _ r b hb, hs]
  simp_rw [target_mul_lattice_root_cartan]
  by_cases h : rootProjection r.val = typeF4SimpleRoot i
  · obtain ⟨j, hj, hr⟩ := hsimple i r h
    subst r
    simp only [if_pos h]
    rw [Finset.sum_eq_single j]
    · simp [hj]
    · intro k _ hk
      have he : typeE6SimpleRootIndex j ≠ typeE6SimpleRootIndex k :=
        fun hh => hk (typeE6SimpleRootIndex_injective hh).symm
      simp only [he, if_false, ite_self]
    · simp
  · simp only [if_neg h]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : node j = i
    · have hr : r ≠ typeE6SimpleRootIndex j := by
        intro hr
        apply h
        rw [hr]
        exact (rootProjection_simple j).trans (congrArg typeF4SimpleRoot hj)
      simp only [hj, if_true, hr, if_false]
    · simp only [hj, if_false]

/-- All four positive comparisons reduce to root-image, simple-fibre and
root-string-length facts for the actual coordinate root systems. -/
theorem firstOrder_positive_of_root_geometry
    (hroot : ∀ r : typeE6Roots, rootProjection r.val ∈ typeF4Roots)
    (hsimple : ∀ (i : Fin 4) (r : typeE6Roots),
      rootProjection r.val = typeF4SimpleRoot i →
        ∃ j : Fin 6, node j = i ∧ r = typeE6SimpleRootIndex j)
    (hchain : ∀ (i : Fin 4) (r : typeE6Roots) (a : typeF4Roots),
      rootProjection r.val = a.val →
        (∑ j : Fin 6, if node j = i then
          typeE6RootPairing.chainBotCoeff (simpleIndex j) r else 0) =
          typeF4RootPairing.chainBotCoeff (sourceIndex i) a)
    (i : Fin 4) :
    foldedOperator true i * latticeMatrix = latticeMatrix * sourceOperator true i := by
  ext (k | r) c
  · obtain ⟨k, rfl⟩ := typeE6RootPairing_baseEquiv.surjective k
    exact firstOrder_cartan_row i k c
  · rcases c with l | a
    · obtain ⟨l, rfl⟩ := typeF4RootPairing_baseEquiv.surjective l
      exact firstOrder_root_cartan hroot hsimple i r l
    · exact firstOrder_root_root hroot hchain i r a

private theorem sourceOperator_false (i : Fin 4) :
    sourceOperator false i = omegaMatrix (b := typeF4RootPairing_base) *
      sourceOperator true i * omegaMatrix (b := typeF4RootPairing_base) := rfl

private theorem targetOperator_false (j : Fin 6) :
    targetOperator false j = omegaMatrix (b := TwistedE6.Base) *
      targetOperator true j * omegaMatrix (b := TwistedE6.Base) := rfl

private theorem foldedOperator_false (i : Fin 4) :
    foldedOperator false i = omegaMatrix (b := TwistedE6.Base) *
      foldedOperator true i * omegaMatrix (b := TwistedE6.Base) := by
  rw [foldedOperator_eq_sum, foldedOperator_eq_sum, Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : node j = i <;> simp [h, targetOperator_false]

/-- The negative comparison follows from the positive comparison by the
actual integral Geck sign involutions. -/
theorem firstOrder_negative_of_positive (i : Fin 4)
    (h : foldedOperator true i * latticeMatrix = latticeMatrix * sourceOperator true i) :
    foldedOperator false i * latticeMatrix = latticeMatrix * sourceOperator false i := by
  let T := omegaMatrix (b := TwistedE6.Base)
  let S := omegaMatrix (b := typeF4RootPairing_base)
  have hω : T * latticeMatrix = latticeMatrix * S := omegaMatrix_intertwines
  rw [foldedOperator_false, sourceOperator_false]
  change T * foldedOperator true i * T * latticeMatrix =
    latticeMatrix * (S * sourceOperator true i * S)
  calc
    T * foldedOperator true i * T * latticeMatrix =
        T * (foldedOperator true i * (T * latticeMatrix)) := by
      simp only [Matrix.mul_assoc]
    _ = T * (foldedOperator true i * (latticeMatrix * S)) := by rw [hω]
    _ = T * (foldedOperator true i * latticeMatrix) * S := by
      simp only [Matrix.mul_assoc]
    _ = T * (latticeMatrix * sourceOperator true i) * S := by rw [h]
    _ = (T * latticeMatrix) * sourceOperator true i * S := by
      simp only [Matrix.mul_assoc]
    _ = (latticeMatrix * S) * sourceOperator true i * S := by rw [hω]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- A matrix comparison acts on the literal integral columns. -/
theorem firstOrder_mulVec_of_matrix (s : Bool) (i : Fin 4)
    (h : foldedOperator s i * latticeMatrix = latticeMatrix * sourceOperator s i)
    (x : SourceIndex → ℤ) :
    foldedOperator s i *ᵥ linearMap ℤ x =
      linearMap ℤ (sourceOperator s i *ᵥ x) := by
  simp only [linearMap, matrix_int, Matrix.mulVecLin_apply]
  rw [Matrix.mulVec_mulVec, h, Matrix.mulVec_mulVec]

section RootGeometryAssembly
variable
    (hroot : ∀ r : typeE6Roots, rootProjection r.val ∈ typeF4Roots)
    (hsimple : ∀ (i : Fin 4) (r : typeE6Roots),
      rootProjection r.val = typeF4SimpleRoot i →
        ∃ j : Fin 6, node j = i ∧ r = typeE6SimpleRootIndex j)
    (hchain : ∀ (i : Fin 4) (r : typeE6Roots) (a : typeF4Roots),
      rootProjection r.val = a.val →
        (∑ j : Fin 6, if node j = i then
          typeE6RootPairing.chainBotCoeff (simpleIndex j) r else 0) =
          typeF4RootPairing.chainBotCoeff (sourceIndex i) a)

include hroot hsimple hchain

/-- The geometric root facts suffice for all eight integral operator
comparisons. Their unconditional construction remains a separate obligation. -/
theorem firstOrder_intertwines_of_root_geometry (s : Bool) (i : Fin 4) :
    foldedOperator s i * latticeMatrix = latticeMatrix * sourceOperator s i := by
  have h := firstOrder_positive_of_root_geometry hroot hsimple hchain i
  cases s
  · exact firstOrder_negative_of_positive i h
  · exact h

/-- Apply the geometric reduction to the literal integral column map used by
the adjoint restriction, retaining both signs and the original node order. -/
theorem firstOrder_mulVec_of_root_geometry (s : Bool) (i : Fin 4) (x : SourceIndex → ℤ) :
    foldedOperator s i *ᵥ linearMap ℤ x =
      linearMap ℤ (sourceOperator s i *ᵥ x) :=
  firstOrder_mulVec_of_matrix s i
    (firstOrder_intertwines_of_root_geometry hroot hsimple hchain s i) x

end RootGeometryAssembly

end TwistedE6.FoldedSubsystem.F4Identification.AdjointRestriction
