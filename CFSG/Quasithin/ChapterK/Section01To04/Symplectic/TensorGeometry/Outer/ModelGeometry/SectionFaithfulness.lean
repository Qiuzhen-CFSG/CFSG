module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Outer.ModelGeometry.SectionFaithfulness.Diagonal
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Outer.ModelGeometry.SectionFaithfulness.Descent

/-!
# Faithfulness of the two Hermitian field sections

The diagonal quotient equivalence intertwines the published middle action
with the natural Sp₄(k) action after entrywise descent and coefficient
Frobenius. Its injectivity proves faithfulness on the middle section.
The equations retain the literal quotient map and native subgroup inclusion,
and transport invariant spaces for every B ≤ C.

For the moved section, the diagonal-kernel theorem puts every symmetric
off-diagonal matrix in the actual displacement space. Fixing these matrices
by congruence forces the actor to be diagonal: multiply each congruence
equation by the inverse transpose and use a third index. The diagonal
entries coincide and have square one, so characteristic two forces the
identity. This proves faithfulness of the published moved action.

Source: Aschbacher–Smith, K.3.4.2, printed pp.456–457, following the
method of H.4.4(6), printed p.381. The common-fixed estimates and the
source-theorem assembly belong to the enclosing model-geometry development.
-/

@[expose] public section

open Matrix Representation
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer.Model.Geometry
noncomputable section
set_option backward.isDefEq.respectTransparency false

section MatrixCalculations
variable {F : Type*} [Field F] [CharP F 2]

private lemma third_index (i j : Index) : ∃ l : Index, l ≠ i ∧ l ≠ j := by
  exact (by decide : ∀ i j : Index, ∃ l : Index, l ≠ i ∧ l ≠ j) i j

private def offDiagonal (i j : Index) : Mat (F := F) :=
  Matrix.single i j 1 + Matrix.single j i 1

omit [CharP F 2] in
private lemma offDiagonal_congruence (A : Mat (F := F)) (i j a b : Index) :
    (A * offDiagonal (F := F) i j * A.transpose) a b = A a i * A b j + A a j * A b i := by
  simp [offDiagonal, Matrix.mul_apply, Matrix.single_apply, ite_and,
    Finset.sum_add_distrib, mul_add, add_mul]

private lemma eq_one_of_fixes_offDiagonal (g : Sp F)
    (hfix : ∀ i j, g.val * offDiagonal (F := F) i j * g.val.transpose = offDiagonal (F := F) i j) : g = 1 := by
  have hBA : (g⁻¹).val * g.val = (1 : Mat (F := F)) :=
    congrArg Subtype.val (inv_mul_cancel g)
  have he (i j : Index) : g.val * offDiagonal (F := F) i j = offDiagonal (F := F) i j * (g⁻¹).val.transpose := by
    have hh := congrArg (fun M : Mat (F := F) => M * (g⁻¹).val.transpose) (hfix i j)
    rw [Matrix.mul_assoc, ← Matrix.transpose_mul, hBA, Matrix.transpose_one, Matrix.mul_one] at hh
    exact hh
  have hz (a i : Index) (hai : a ≠ i) : g.val a i = 0 := by
    obtain ⟨j, hja, hji⟩ := third_index a i
    have hh := congrArg (fun M : Mat (F := F) => M a j) (he i j)
    simpa [offDiagonal, Matrix.mul_apply, Matrix.single_apply, ite_and,
      Finset.sum_add_distrib, mul_add, add_mul, hai, Ne.symm hai, hja, Ne.symm hja,
      hji, Ne.symm hji] using hh
  have hp (i j : Index) (hij : i ≠ j) : g.val i i * g.val j j = 1 := by
    have hh := congrArg (fun M : Mat (F := F) => M i j) (hfix i j)
    rw [offDiagonal_congruence, hz i j hij] at hh
    simpa [offDiagonal, Matrix.single_apply, hij, Ne.symm hij] using hh
  have hd (i j : Index) (hij : i ≠ j) : g.val i i = (g⁻¹).val j j := by
    have hh := congrArg (fun M : Mat (F := F) => M i j) (he i j)
    simpa [offDiagonal, Matrix.mul_apply, Matrix.single_apply, ite_and,
      Finset.sum_add_distrib, mul_add, add_mul, hij, Ne.symm hij] using hh
  have hc (i j : Index) : g.val i i = g.val j j := by
    obtain ⟨l, hli, hlj⟩ := third_index i j
    exact (hd i l (Ne.symm hli)).trans (hd j l (Ne.symm hlj)).symm
  have hone (i : Index) : g.val i i = 1 := by
    obtain ⟨j, hji, _⟩ := third_index i i
    have hh := hp i j (Ne.symm hji)
    rw [← hc i j] at hh
    apply frobenius_inj F 2
    simpa [frobenius_def, pow_two] using hh
  apply Subtype.ext
  ext i j
  by_cases hij : i = j
  · subst j; simpa using hone i
  · simpa [Matrix.one_apply, hij] using hz i j hij


private lemma congruence_diagonal (A X : Mat (F := F)) (hX : X.transpose = X) (i : Index) :
    (A * X * A.transpose) i i = ∑ j, A i j ^ 2 * X j j := by
  have hs (a b : Index) : X b a = X a b := congrFun (congrFun hX a) b
  have hoff : (∑ ab : Index × Index,
      if ab.1 = ab.2 then 0 else A i ab.1 * A i ab.2 * X ab.1 ab.2) = 0 := by
    apply Finset.sum_involution (fun ab _ => ab.swap)
    · intro ab _
      dsimp
      by_cases h : ab.1 = ab.2
      · simp [h]
      · simp only [h, Ne.symm h, if_false]
        rw [hs ab.1 ab.2, mul_comm (A i ab.2) (A i ab.1)]
        exact CharTwo.add_self_eq_zero _
    · intro ab _ hne heq
      have h : ab.1 = ab.2 := (congrArg Prod.fst heq).symm
      exact hne (by simp [h])
    · intro ab _
      exact Prod.swap_swap ab
    · intro ab _
      exact Finset.mem_univ _
  calc
    (A * X * A.transpose) i i = ∑ a, ∑ b, A i a * A i b * X a b := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = ∑ a, ∑ b, ((if a = b then A i a ^ 2 * X a a else 0) +
        (if a = b then 0 else A i a * A i b * X a b)) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      by_cases h : a = b <;> simp [h, pow_two]
    _ = (∑ a, A i a ^ 2 * X a a) +
        (∑ ab : Index × Index, if ab.1 = ab.2 then 0 else A i ab.1 * A i ab.2 * X ab.1 ab.2) := by
      simp [Finset.sum_add_distrib, Fintype.sum_prod_type]
    _ = _ := by rw [hoff, add_zero]

end MatrixCalculations

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
  (σ : F ≃ₐ[k] F) (hσ : Function.Involutive σ)
  [FiniteDimensional k F] (hdeg : Module.finrank k F = 2) (hne : σ ≠ AlgEquiv.refl)
  [CharP F 2]

local instance : AddCommGroup (Space σ hσ) := inferInstance
local instance : AddCommGroup (fieldFixed σ hσ) := inferInstance
local instance : AddCommGroup (fieldMoved σ hσ) := inferInstance

/-- The diagonal map intertwines the native fixed-space action with squared descended entries. -/
lemma diagonalMap_fixedAction [CharP k 2] (g : centralizer σ) (X : fieldFixed σ hσ) :
    diagonalMap σ hσ hdeg hne (fixedAction σ hσ g X) =
      symplecticNatural 2 (frobeniusDescent σ hdeg hne g) (diagonalMap σ hσ hdeg hne X) := by
  ext i
  apply (algebraMap k F).injective
  rw [diagonalMap_entry]
  change (g.val.val * X.val.val * (g.val.val.map σ).transpose) i i =
    algebraMap k F (((frobeniusDescent σ hdeg hne g).val).mulVec
      (diagonalMap σ hσ hdeg hne X) i)
  rw [centralizer_map, congruence_diagonal _ _ ((mem_fieldFixed σ hσ X.val).mp X.property)]
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul,
    frobeniusDescent_entry, map_pow, centralizerDescent_entry, diagonalMap_entry]

/-- The actual middle quotient is the natural representation after descent and coefficient Frobenius. -/
lemma middleEquiv_intertwines [CharP k 2] (g : centralizer σ) (X : Middle σ hσ) :
    middleEquiv σ hσ hdeg hne (middleAction σ hσ g X) =
      symplecticNatural 2 (frobeniusDescent σ hdeg hne g) (middleEquiv σ hσ hdeg hne X) := by
  induction X using Submodule.Quotient.induction_on with
  | _ X =>
    change diagonalMap σ hσ hdeg hne (fixedAction σ hσ g X) =
      symplecticNatural 2 (frobeniusDescent σ hdeg hne g) (diagonalMap σ hσ hdeg hne X)
    exact diagonalMap_fixedAction σ hσ hdeg hne g X

include hdeg hne in
/-- Faithfulness of the published action on the literal fixed/displacement quotient. -/
theorem middleAction_faithful [CharP k 2] : Function.Injective (middleAction σ hσ) := by
  intro g h he
  apply frobeniusDescent_injective σ hdeg hne
  apply Subtype.ext
  apply Matrix.mulVec_injective
  funext v
  obtain ⟨X, rfl⟩ := (middleEquiv σ hσ hdeg hne).surjective v
  change symplecticNatural 2 (frobeniusDescent σ hdeg hne g) _ =
    symplecticNatural 2 (frobeniusDescent σ hdeg hne h) _
  rw [← middleEquiv_intertwines, ← middleEquiv_intertwines, he]

private def symmetricUnit (i j : Index) : Space σ hσ :=
  ⟨offDiagonal (F := F) i j, by
    ext a b
    simp [offDiagonal, adjoint, Matrix.single_apply, add_comm, and_comm]⟩

omit [FiniteDimensional k F] [CharP F 2] in
private lemma symmetricUnit_mem_fixed (i j : Index) : symmetricUnit σ hσ i j ∈ fieldFixed σ hσ := by
  rw [mem_fieldFixed]
  simp [symmetricUnit, offDiagonal, add_comm]

include hdeg hne in
private lemma symmetricUnit_mem_moved (i j : Index) : symmetricUnit σ hσ i j ∈ fieldMoved σ hσ := by
  have hh : (⟨symmetricUnit σ hσ i j, symmetricUnit_mem_fixed σ hσ i j⟩ : fieldFixed σ hσ) ∈
      LinearMap.ker (diagonalMap σ hσ hdeg hne) := by
    rw [mem_ker_diagonalMap]
    intro a
    simp [symmetricUnit, offDiagonal, Matrix.single_apply, and_comm, CharTwo.add_self_eq_zero]
  rw [ker_diagonalMap] at hh
  exact hh

include hdeg hne in
/-- Faithfulness of the published action on the literal displacement subspace. -/
theorem movedAction_faithful : Function.Injective (movedAction σ hσ) := by
  apply (injective_iff_map_eq_one (movedAction σ hσ)).mpr
  intro g hg
  apply Subtype.ext
  apply eq_one_of_fixes_offDiagonal
  intro i j
  have he := congrArg (fun f : (fieldMoved σ hσ) →ₗ[k] fieldMoved σ hσ =>
    (f ⟨symmetricUnit σ hσ i j, symmetricUnit_mem_moved σ hσ hdeg hne i j⟩).val.val) hg
  change g.val.val * offDiagonal (F := F) i j * (g.val.val.map σ).transpose = offDiagonal (F := F) i j at he
  rwa [centralizer_map] at he

/-- Restriction retains the original subgroup inclusion and quotient action. -/
lemma middleEquiv_restrict_intertwines [CharP k 2]
    (B : Subgroup (Sp F)) (hB : B ≤ centralizer σ) (g : B) (X : Middle σ hσ) :
    middleEquiv σ hσ hdeg hne
        (((middleAction σ hσ).comp (Subgroup.inclusion hB)) g X) =
      (((symplecticNatural 2).comp
        ((frobeniusDescent σ hdeg hne).comp (Subgroup.inclusion hB))) g)
        (middleEquiv σ hσ hdeg hne X) :=
  middleEquiv_intertwines σ hσ hdeg hne (Subgroup.inclusion hB g) X

/-- Invariants of every native subgroup are transported by the actual diagonal quotient map. -/
def middleInvariantsEquiv [CharP k 2] (B : Subgroup (Sp F)) (hB : B ≤ centralizer σ) :
    Representation.invariants ((middleAction σ hσ).comp (Subgroup.inclusion hB)) ≃ₗ[k]
      Representation.invariants ((symplecticNatural 2).comp
        ((frobeniusDescent σ hdeg hne).comp (Subgroup.inclusion hB))) where
  toFun X := ⟨middleEquiv σ hσ hdeg hne X.val, by
    intro b
    change symplecticNatural 2 (frobeniusDescent σ hdeg hne (Subgroup.inclusion hB b)) _ = _
    rw [← middleEquiv_intertwines]
    exact congrArg (middleEquiv σ hσ hdeg hne) (X.property b)⟩
  invFun X := ⟨(middleEquiv σ hσ hdeg hne).symm X.val, by
    intro b
    apply (middleEquiv σ hσ hdeg hne).injective
    change middleEquiv σ hσ hdeg hne (middleAction σ hσ (Subgroup.inclusion hB b) _) = _
    rw [middleEquiv_intertwines, LinearEquiv.apply_symm_apply]
    exact X.property b⟩
  left_inv X := Subtype.ext ((middleEquiv σ hσ hdeg hne).symm_apply_apply X.val)
  right_inv X := Subtype.ext ((middleEquiv σ hσ hdeg hne).apply_symm_apply X.val)
  map_add' X Y := Subtype.ext (map_add (middleEquiv σ hσ hdeg hne) X.val Y.val)
  map_smul' c X := Subtype.ext (map_smul (middleEquiv σ hσ hdeg hne) c X.val)

lemma finrank_middleInvariants_eq [CharP k 2] (B : Subgroup (Sp F)) (hB : B ≤ centralizer σ) :
    Module.finrank k (Representation.invariants
        ((middleAction σ hσ).comp (Subgroup.inclusion hB))) =
      Module.finrank k (Representation.invariants ((symplecticNatural 2).comp
        ((frobeniusDescent σ hdeg hne).comp (Subgroup.inclusion hB)))) :=
  (middleInvariantsEquiv σ hσ hdeg hne B hB).finrank_eq


end
end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer.Model.Geometry
