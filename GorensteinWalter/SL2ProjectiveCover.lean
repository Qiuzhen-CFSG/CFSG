module

public import GorensteinWalter.PSL2DihedralSylow
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# The canonical SL2 projective two-cover

Over a finite odd field, the actual quotient map SL2(F) -> PSL2(F) is
surjective with central kernel of order two, hence a two-group kernel.
Every Sylow two-subgroup of the projective group has a finite nontrivial
dihedral model. If the field has more than three elements, SL2(F) is perfect:
an element outside {0,1,-1} supplies the diagonal commutator used by the
Mathlib transvection-generation proof.

These facts provide the reference cover for the two-primary comparison in
ABG Chapter II, Section 3, Proposition 2 (article page 22). The kernel count
uses the existing scalar-center/roots-of-unity equivalence and odd-field
root count; the Sylow model uses the proved split/nonsplit torus theorem.
The perfectness hypothesis retains order nine, while the kernel and Sylow
theorems separately include order three. The odd-cardinality characteristic
test is public for consumers of the odd-field SL2 no-index-two theorem.
No cover-recognition conclusion or
Schur-multiplier bound is assumed. This model adapter stays above Theory
because its proved torus-model dependency lives in GorensteinWalter.
-/

public section
noncomputable section
namespace GorensteinWalter

/-- The canonical projection, with its actual central quotient exposed. -/
@[expose] def sl2ProjectiveProjection (F : Type*) [Field F] :
    Matrix.SpecialLinearGroup (Fin 2) F →* PSL2 F :=
  QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))

theorem sl2ProjectiveProjection_surjective (F : Type*) [Field F] :
    Function.Surjective (sl2ProjectiveProjection F) :=
  QuotientGroup.mk'_surjective _

theorem sl2ProjectiveProjection_ker (F : Type*) [Field F] :
    (sl2ProjectiveProjection F).ker =
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
  QuotientGroup.ker_mk' _

private theorem field_odd_prime_power (F : Type*) [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) : IsOddPrimePower (Nat.card F) := by
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  have hcard : Nat.card F = ringChar F ^ (n : ℕ) := by
    simpa only [Nat.card_eq_fintype_card] using hn
  refine ⟨ringChar F, n, hp, ?_, n.pos, hcard⟩
  apply hp.odd_of_ne_two
  intro htwo
  rw [htwo] at hcard
  have heven : Even (Nat.card F) := by
    rw [hcard]
    exact (Nat.even_pow.mpr ⟨by decide, n.pos.ne'⟩)
  exact (Nat.not_even_iff_odd.mpr hodd) heven

theorem two_ne_zero_of_odd_card (F : Type*) [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) : (2 : F) ≠ 0 := by
  let : Fintype F := Fintype.ofFinite F
  apply Ring.two_ne_zero
  intro hchar
  have heven := FiniteField.even_card_of_char_two (F := F) hchar
  have hodd' : Odd (Fintype.card F) := by simpa [Nat.card_eq_fintype_card] using hodd
  exact (Nat.not_even_iff_odd.mpr hodd') (Nat.even_iff.mpr heven)

theorem sl2ProjectiveProjection_ker_card
    (F : Type*) [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    Nat.card (sl2ProjectiveProjection F).ker = 2 := by
  rw [sl2ProjectiveProjection_ker]
  let e := Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity'
    (i := (0 : Fin 2)) (R := F)
  rw [Nat.card_congr e.toEquiv]
  exact rootsOfUnity_two_of_char_ne_two F (two_ne_zero_of_odd_card F hodd)

theorem sl2ProjectiveProjection_ker_isPGroup
    (F : Type*) [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    IsPGroup 2 (sl2ProjectiveProjection F).ker := by
  apply IsPGroup.of_card (n := 1)
  simpa only [pow_one] using sl2ProjectiveProjection_ker_card F hodd

theorem sl2_isPerfect_of_card_gt_three
    (F : Type*) [Field F] [Finite F] (hcard : 3 < Nat.card F) :
    Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hex : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
    by_contra h
    push Not at h
    have hsubset : (Finset.univ : Finset F) ⊆ {0, 1, -1} := by
      intro a _
      by_cases ha : a = 0
      · simp [ha]
      · rcases sq_eq_one_iff.mp (h a ha) with h1 | hneg
        · simp [h1]
        · simp [hneg]
    have hc := Finset.card_le_card hsubset
    have hthree : ({0, 1, -1} : Finset F).card ≤ 3 := by
      exact (Finset.card_insert_le _ _).trans (by
        have := Finset.card_insert_le (1 : F) {-1}
        simpa using Nat.add_le_add_right this 1)
    have hle : Nat.card F ≤ 3 := by
      simpa only [Finset.card_univ, ← Nat.card_eq_fintype_card] using hc.trans hthree
    exact (not_lt_of_ge hle) hcard
  obtain ⟨a, ha, hasq⟩ := hex
  exact ⟨Matrix.SL2.commutator_eq_top ha hasq⟩

theorem psl2_dihedral_sylow_of_odd_card
    (F : Type*) [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (S : Sylow 2 (PSL2 F)) :
    ∃ n : ℕ, 0 < n ∧ Nonempty (S ≃* DihedralGroup n) := by
  obtain ⟨m, _, hm⟩ := psl2_odd_hasDihedralSylowTwo_model F
    (field_odd_prime_power F hodd) S
  exact ⟨2 ^ m, by positivity, hm⟩

/-- The complete reference-cover data used by the two-primary comparison. -/
theorem sl2_projective_cover_model
    (F : Type*) [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (hcard : 3 < Nat.card F) :
    Function.Surjective (sl2ProjectiveProjection F) ∧
      (sl2ProjectiveProjection F).ker ≤
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) ∧
      Nat.card (sl2ProjectiveProjection F).ker = 2 ∧
      IsPGroup 2 (sl2ProjectiveProjection F).ker ∧
      Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) ∧
      ∀ S : Sylow 2 (PSL2 F),
        ∃ n : ℕ, 0 < n ∧ Nonempty (S ≃* DihedralGroup n) := by
  exact ⟨sl2ProjectiveProjection_surjective F,
    (sl2ProjectiveProjection_ker F).le,
    sl2ProjectiveProjection_ker_card F hodd,
    sl2ProjectiveProjection_ker_isPGroup F hodd,
    sl2_isPerfect_of_card_gt_three F hcard,
    psl2_dihedral_sylow_of_odd_card F hodd⟩

end GorensteinWalter
