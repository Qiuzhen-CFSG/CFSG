module

public import Theory.SpecificGroups.PSL3Three.FourNormalizer.Conjugacy
public import Theory.SpecificGroups.PSL3Three.GraphWitnesses.EightCentralizers.GraphModel.IsotropicLines
public import Theory.SpecificGroups.PSL3Three.MonomialMaximality
public import Theory.SpecificGroups.PSL3Three.Simplicity

/-!
# Normalizer and centralizer of the diagonal four in SL₃(3)

The monomial subgroup normalizes the diagonal four, by its signed column
matrices. Maximality of that subgroup and simplicity give the full normalizer.
Commuting with two independent diagonal involutions forces a matrix to be
diagonal, so the four is self-centralizing. The action on the four isotropic
lines identifies its normalizer with S₄.

Source: Aschbacher--Smith, quasithin manuscript, Lemma 2.5.8(5), pp.556--557.
-/

public section
namespace Matrix.PSL3Three.FourGeometry
open Subgroup

private def signedVector : Fin 6 → Fin 3 → ZMod 3 :=
  ![![1, 0, 0], ![2, 0, 0], ![0, 1, 0], ![0, 2, 0], ![0, 0, 1], ![0, 0, 2]]
private def signedMatrix (w : Fin 3 → Fin 6) : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  fun i j => signedVector (w j) i
private theorem signedVector_surjective : ∀ v : Fin 3 → ZMod 3,
    v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 → ∃ i, signedVector i = v := by decide
private theorem signedMatrix_normalizes : ∀ w : Fin 3 → Fin 6,
    (signedMatrix w).det = 1 → ∀ i : Fin 4, ∃ j : Fin 4,
    signedMatrix w * (diagonalElement i).val = (diagonalElement j).val * signedMatrix w := by
  decide +kernel

private theorem exists_signedMatrix (g : monomialSL) :
    ∃ w, signedMatrix w = g.val.val := by
  have hc := (mem_monomialSL_iff_columns g.val).mp g.property
  have he (j : Fin 3) : ∃ i, signedVector i = fun k => g.val.val k j :=
    signedVector_surjective _ (hc j)
  choose w hw using he
  exact ⟨w, by ext i j; exact congrFun (hw j) i⟩

private theorem diagonal_le_monomial : diagonalFour ≤ monomialSL := by
  rintro _ ⟨i, rfl⟩
  rw [mem_monomialSL_iff_columns]
  revert i
  decide

private theorem monomial_le_normalizer : monomialSL ≤ normalizer (diagonalFour : Set SL) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x, ⟨i, rfl⟩, rfl⟩
    obtain ⟨w, hw⟩ := exists_signedMatrix ⟨g, hg⟩
    obtain ⟨j, hj⟩ := signedMatrix_normalizes w (hw ▸ g.property) i
    have he : g * diagonalElement i = diagonalElement j * g := by
      apply Subtype.ext
      change g.val * (diagonalElement i).val = (diagonalElement j).val * g.val
      simpa only [hw] using hj
    exact ⟨j, by change diagonalElement j = g * diagonalElement i * g⁻¹
                 rw [he, mul_inv_cancel_right]⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

/-- The full normalizer of the diagonal four is the actual monomial subgroup. -/
theorem normalizer_diagonalFour : normalizer (diagonalFour : Set SL) = monomialSL := by
  let : IsSimpleGroup PSL := isSimpleGroup_psl3_three
  let : IsSimpleGroup SL := equiv.isSimpleGroup
  rcases isCoatom_monomialSL.le_iff.mp monomial_le_normalizer with htop | heq
  · rcases (normalizer_eq_top_iff.mp htop).eq_bot_or_eq_top with hbot | htop
    · have h1 : Nat.card diagonalFour = 1 := Subgroup.card_eq_one.mpr hbot
      rw [card_diagonalFour] at h1
      omega
    · exact (isCoatom_monomialSL.ne_top (top_unique (htop ▸ diagonal_le_monomial))).elim
  · exact heq

private theorem commuting_block_diagonal : ∀ a b c d e : ZMod 3,
    let M : Matrix (Fin 3) (Fin 3) (ZMod 3) := !![a,b,0; c,d,0; 0,0,e]
    M.det = 1 → M * (diagonalElement 2).val = (diagonalElement 2).val * M →
      ∃ i : Fin 4, (diagonalElement i).val = M := by decide

/-- The diagonal four is its own full centralizer. -/
theorem centralizer_diagonalFour : centralizer (diagonalFour : Set SL) = diagonalFour := by
  apply le_antisymm
  · intro u hu
    have hz : u ∈ centralizer ({Matrix.SL3.standardInvolution (ZMod 3)} : Set SL) := by
      apply mem_centralizer_singleton_iff.mpr
      exact (hu (diagonalElement 1) ⟨1, rfl⟩).symm
    have hoff := (Matrix.SL3.mem_standardInvolution_centralizer_iff (ZMod 3)
      (by decide) u).mp hz
    have he : u.val = !![u 0 0, u 0 1, 0; u 1 0, u 1 1, 0; 0, 0, u 2 2] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp_all
    obtain ⟨i, hi⟩ := commuting_block_diagonal (u 0 0) (u 0 1) (u 1 0) (u 1 1) (u 2 2)
      (by rw [← he]; exact u.property)
      (by rw [← he]; exact congrArg Subtype.val (hu (diagonalElement 2) ⟨2, rfl⟩).symm)
    exact ⟨i, Subtype.ext (hi.trans he.symm)⟩
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    have h : ∀ i j : Fin 4, diagonalElement j * diagonalElement i =
      diagonalElement i * diagonalElement j := by decide
    exact h i j

/-- Its literal normalizer acts faithfully and fully on the four isotropic lines. -/
noncomputable def diagonalFourNormalizerEquiv :
    normalizer (diagonalFour : Set SL) ≃* Equiv.Perm (Fin 4) :=
  (MulEquiv.subgroupCongr normalizer_diagonalFour).trans
    GraphWitnesses.EightCentralizers.GraphModel.monomialEquivSymmetricFour

end Matrix.PSL3Three.FourGeometry
