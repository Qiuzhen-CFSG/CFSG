module

public import Theory.SpecificGroups.PSL3.SylowFixedActions.Standard.Model
public import Mathlib.GroupTheory.Sylow

/-!
# A two-subgroup containing the projective test matrices

The fourth-power kernel in the product of two unit groups maps to a diagonal
two-subgroup of SL₃. The determinant-one interchange swaps its parameters,
so adjoining the interchange still gives a two-subgroup. Its actual projective
image contains both diagonal tests and the interchange. Sylow containment can
therefore be used without computing the order of SL₃ or PSL₃.

Source: the monomial matrices in GLS3, §2.7, and the linear cases of
Aschbacher–Smith F.6.18(10)–(11), printed pp.309–310, used in 15.4.18,
printed pp.1162–1163.
-/

public section
open scoped MatrixGroups
namespace Matrix.PSL3.SylowFixedActions.Standard
variable (F : Type*) [Field F]

private theorem interchange_inv : (interchange F)⁻¹ = interchange F :=
  inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using interchange_sq F)

theorem interchange_diagonalSL (u : Fˣ × Fˣ) :
    interchange F * diagonalSL F u * (interchange F)⁻¹ = diagonalSL F (u.2, u.1) := by
  rw [interchange_inv]
  apply Subtype.ext
  change (!![0, 1, 0; 1, 0, 0; 0, 0, -1] : Matrix (Fin 3) (Fin 3) F) *
    Matrix.diagonal ![(u.1 : F), (u.2 : F), ((u.1 * u.2)⁻¹ : Fˣ)] *
    !![0, 1, 0; 1, 0, 0; 0, 0, -1] =
    Matrix.diagonal ![(u.2 : F), (u.1 : F), ((u.2 * u.1)⁻¹ : Fˣ)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal, mul_comm, Matrix.vecHead, Matrix.vecTail]

/-- A two-subgroup contains the three projective tests. It need not be
identified as a Sylow subgroup, nor does this compute the order of PSL₃. -/
theorem exists_two_subgroup_containing_tests (u : Fˣ) (hu : u ^ 4 = 1) :
    ∃ Q : Subgroup PSL(3, F), IsPGroup 2 Q ∧ testSet F u ⊆ Q := by
  let K := (powMonoidHom 4 : (Fˣ × Fˣ) →* (Fˣ × Fˣ)).ker
  let D := K.map (diagonalSL F)
  have hK : IsPGroup 2 K := by
    intro a
    refine ⟨2, ?_⟩
    apply Subtype.ext
    exact a.property
  have hD : IsPGroup 2 D := hK.map (diagonalSL F)
  have hconj : ∀ x ∈ D, interchange F * x * (interchange F)⁻¹ ∈ D := by
    rintro x ⟨a, ha, rfl⟩
    refine ⟨(a.2, a.1), ?_, (interchange_diagonalSL F a).symm⟩
    change (a.2, a.1) ^ 4 = (1 : Fˣ × Fˣ)
    change a ^ 4 = 1 at ha
    apply Prod.ext
    · exact congrArg Prod.snd ha
    · exact congrArg Prod.fst ha
  have hn : interchange F ∈ Subgroup.normalizer D := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconj x, fun hx => ?_⟩
    have hh := hconj _ hx
    have heq : interchange F * (interchange F * x * (interchange F)⁻¹) *
        (interchange F)⁻¹ = x := by
      calc
        _ = interchange F ^ 2 * x * (interchange F ^ 2)⁻¹ := by
          simp only [pow_two, _root_.mul_inv_rev, mul_assoc]
        _ = x := by rw [interchange_sq]; simp
    rwa [heq] at hh
  have hw : IsPGroup 2 (Subgroup.zpowers (interchange F)) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one (interchange_sq F))
  let Q := D ⊔ Subgroup.zpowers (interchange F)
  have hQ : IsPGroup 2 Q := hD.to_sup_of_normal_left' hw (Subgroup.zpowers_le.mpr hn)
  refine ⟨Q.map (projection F), hQ.map (projection F), ?_⟩
  intro x hx
  simp only [testSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · apply Subgroup.mem_map_of_mem
    apply (le_sup_left : D ≤ Q)
    refine ⟨(u, u⁻¹), ?_, rfl⟩
    change (u, u⁻¹) ^ 4 = (1 : Fˣ × Fˣ)
    apply Prod.ext
    · exact hu
    · change u⁻¹ ^ 4 = 1
      rw [inv_pow, hu, inv_one]
  · apply Subgroup.mem_map_of_mem
    apply (le_sup_left : D ≤ Q)
    refine ⟨(1, u), ?_, rfl⟩
    change ((1 : Fˣ), u) ^ 4 = (1 : Fˣ × Fˣ)
    apply Prod.ext
    · exact one_pow 4
    · exact hu
  · exact Subgroup.mem_map_of_mem (projection F)
      ((le_sup_right : Subgroup.zpowers (interchange F) ≤ Q) (Subgroup.mem_zpowers _))

end Matrix.PSL3.SylowFixedActions.Standard
