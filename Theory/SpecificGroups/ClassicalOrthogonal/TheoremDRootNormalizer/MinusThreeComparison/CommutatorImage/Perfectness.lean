module
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison.Descent
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourGeneration
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointResidual
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneRadical.Levi

/-!
# Perfectness and commutator containment for the unitary exterior image

For a nonbinary fixed field, the actual SU₄ vector stabilizer is perfect.
The plane Levi copy of SL₂ over the extension field is also perfect. Its
diagonal elements supply every scalar on the first isotropic point, so these
two perfect subgroups contain the point parabolic in the derived subgroup.
The plane Levi also contains the adjacent coordinate swap. The explicit
unitary elimination theorem then proves that the whole special unitary group
is perfect, and hence its descended exterior image lies in the literal
commutator of the full quadratic isometry group.

This proves containment only; exhaustion still requires the minus-form image
normality argument. No orthogonal order, elementary-group identification or
simplicity theorem is used here. Sources: GLS3 §2.7, especially the classical
unitary and even orthogonal conventions on printed pp.85–89, and the concrete
unitary local and generation results cited in the imported modules.
-/

public noncomputable section
namespace ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison
open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPointLocal UnitaryFourGeneration

private theorem image_mem_commutator {G H : Type*} [Group G] [Group H]
    [Group.IsPerfect G] (f : G →* H) (g : G) : f g ∈ commutator H := by
  have hm := map_derivedSeries_le_derivedSeries f 1
  rw [derivedSeries_one, derivedSeries_one, Group.IsPerfect.commutator_eq_top] at hm
  exact hm ⟨g, Subgroup.mem_top _, rfl⟩

private theorem antidiagonal_isPerfect (F : Type*) [_root_.Field F] [Finite F] [CharP F 2]
    (σ : F ≃+* F) (hσ : Function.Involutive σ) (hnt : ∃ x, σ x ≠ x)
    (a : FixedBy.subfield F σ) (ha : a ≠ 0) (ha1 : a ≠ 1) :
    Group.IsPerfect (UnitaryFourFlag.SU F (UnitaryFourFlag.form F σ hσ)) := by
  let J := UnitaryFourFlag.form F σ hσ
  let D := commutator (UnitaryFourFlag.SU F J)
  let L := localSU F J
  let : Group.IsPerfect L := UnitaryFourPointResidual.localSU_isPerfect F σ hσ hnt a ha ha1
  have hL : L ≤ D := fun g hg => image_mem_commutator L.subtype ⟨g, hg⟩
  have haF : (a : F) ≠ 0 := fun h => ha (Subtype.ext h)
  have haF1 : (a : F) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have haF2 : (a : F) ^ 2 ≠ 1 := by
    intro h
    rcases sq_eq_one_iff.mp h with h | h
    · exact haF1 h
    · exact haF1 (by simpa only [CharTwo.neg_eq] using h)
  let : Group.IsPerfect (SpecialLinearGroup (Fin 2) F) :=
    ⟨Matrix.SL2.commutator_eq_top haF haF2⟩
  let f : SpecialLinearGroup (Fin 2) F →* UnitaryFourFlag.SU F J :=
    (UnitaryFourPlaneLocal.localFactor F J).subtype.comp
      (UnitaryFourPlaneRadical.levi F σ hσ)
  have hf (A : SpecialLinearGroup (Fin 2) F) :
      UnitaryFourPlaneRadical.leviSU F σ hσ A ∈ D := image_mem_commutator f A
  have hP : pointParabolicSU F J ≤ D := by
    intro g hg
    obtain ⟨h1,h2,h3⟩ := (mem_pointParabolicSU F J g).mp hg
    have ht : g.val.val 0 0 ≠ 0 := by
      intro ht
      apply GeneralLinearGroup.det_ne_zero g.val
      apply Matrix.det_eq_zero_of_column_eq_zero 0
      intro i
      fin_cases i <;> assumption
    let A := SpecialLinearGroup.diag2 (g.val.val 0 0)⁻¹ (inv_ne_zero ht)
    let l := UnitaryFourPlaneRadical.leviSU F σ hσ A
    have hl : g * l ∈ L := by
      rw [mem_localSU]
      change (g.val.val * (UnitaryFourPlaneRadical.leviMatrix F σ A)) 0 0 = 1 ∧
        (g.val.val * (UnitaryFourPlaneRadical.leviMatrix F σ A)) 1 0 = 0 ∧
        (g.val.val * (UnitaryFourPlaneRadical.leviMatrix F σ A)) 2 0 = 0 ∧
        (g.val.val * (UnitaryFourPlaneRadical.leviMatrix F σ A)) 3 0 = 0
      simp [UnitaryFourPlaneRadical.leviMatrix, A, SpecialLinearGroup.diag2_coe',
        Matrix.mul_apply, Fin.sum_univ_succ, h1,h2,h3, mul_inv_cancel₀ ht]
    exact (D.mul_mem_cancel_right (hf A)).mp (hL hl)
  have hs : pairSwap F σ hσ ∈ D := by
    let A : SpecialLinearGroup (Fin 2) F := ⟨!![0,1;1,0], by
      simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩
    have he : UnitaryFourPlaneRadical.leviSU F σ hσ A = pairSwap F σ hσ := by
      apply Subtype.ext
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [UnitaryFourPlaneRadical.leviSU, UnitaryFourPlaneRadical.leviMatrix,
          A, pairSwap, involutionElement, pairSwapMatrix]
    exact he ▸ hf A
  exact ⟨eq_top_of_point_and_pairSwap F σ hσ D hP hs⟩

variable (n : ℕ) [NeZero n]

/-- SU₄ over the quadratic binary extension is perfect when the fixed field
has more than two elements. -/
theorem su_isPerfect (hn : 1 < n) : Group.IsPerfect (SU n) := by
  let : Fintype (FixedField n) := Fintype.ofFinite _
  have hcard : 3 ≤ 2 ^ n := by
    have h := Nat.pow_le_pow_right (n := 2) (by decide) (show 2 ≤ n by omega)
    omega
  obtain ⟨a, ha, ha1⟩ := ENat.exists_ne_ne_of_three_le
    (α := FixedField n) (by
      rw [ENat.card_eq_coe_fintype_card, ← Nat.card_eq_fintype_card, card_fixedField]
      exact_mod_cast hcard) 0 1
  exact antidiagonal_isPerfect (Field n) (conjugation n)
    (Representation.OrthogonalFourMinus.FiniteModel.conjugation_involutive n)
    (Representation.OrthogonalFourMinus.FiniteModel.exists_conjugation_ne n) a ha ha1

/-- The actual descended exterior action takes values in the full orthogonal
commutator, as follows from perfectness of its special unitary source. -/
theorem orthogonalAction_range_le_commutator (hn : 1 < n) (hD : Descends n) :
    (orthogonalAction n hD).range ≤ commutator (FullOrthogonal n) := by
  let : Group.IsPerfect (SU n) := su_isPerfect n hn
  rintro g ⟨s, rfl⟩
  exact image_mem_commutator (orthogonalAction n hD) s

end ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison
