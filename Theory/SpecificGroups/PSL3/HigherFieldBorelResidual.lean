module

public import Theory.SpecificGroups.PSL3.CartanActions
public import Theory.GroupTheory.PPerfectHom
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Two-perfectness of the concrete degree-three Borel

Over a finite field of characteristic two with more than two elements,
the diagonal subgroups have odd order. Hence they vanish in every two-group
quotient of the upper triangular Borel. Conjugating an upper root element
by diag(a,a⁻¹,1), in the positions of that root, multiplies its parameter by
a². Choose a nonidentity unit, so that a²-1 is nonzero. The resulting
commutators exhaust each upper root group. Triangular factorization then
shows that every such quotient is trivial. The assertion descends along
the actual projection to PSL₃, including fields with a nontrivial center.

Source: the Borel residual calculations used in Aschbacher–Smith,
combined manuscript (1 March 2004), proof of 13.8.20,
printed pp.954–955 (PDF pp.971–972). The matrix models and their inherited
ATLAS attribution are those of the imported projective group development.
-/

@[expose] public section

open Matrix Matrix.SpecialLinearGroup Matrix.PSL3 Matrix.PSL3.LinearThree
open Matrix.PSL3.CartanActions
open scoped MatrixGroups commutatorElement
namespace Matrix.PSL3.HigherFieldBorelResidual
variable {F : Type*} [Field F] [Finite F]

private lemma diag_mem {i j : Fin 3} (hij : i ≠ j) (a : Fˣ) :
    diag2n hij (a : F) a.ne_zero ∈ borelSL F := by
  rw [mem_borelSL_iff, diag2n_coe]
  simp

private noncomputable def diagonalHom {i j : Fin 3} (hij : i ≠ j) : Fˣ →* borelSL F where
  toFun a := ⟨diag2n hij (a : F) a.ne_zero, diag_mem hij a⟩
  map_one' := by
    apply Subtype.ext; apply Subtype.ext
    simp [diag2n_coe]
  map_mul' a b := by
    apply Subtype.ext; apply Subtype.ext
    change diagonal _ = diagonal _ * diagonal _
    rw [diagonal_mul_diagonal]
    congr 1
    ext k
    by_cases hi : k = i <;> by_cases hj : k = j <;>
      simp [hi, hj, hij.symm, mul_comm]

private lemma root_mem {i j : Fin 3} (hij : i < j) (t : F) :
    SpecialLinearGroup.transvection (ne_of_lt hij) t ∈ borelSL F := by
  rw [mem_borelSL_iff]
  fin_cases i <;> fin_cases j <;> simp only [Fin.lt_def] at hij <;> try omega
  all_goals simp [transvection_coe]

private lemma diagonal_commutator {i j : Fin 3} (hij : i < j) (a : Fˣ) (t : F) :
    ⁅(diagonalHom (ne_of_lt hij) a : borelSL F),
      (⟨SpecialLinearGroup.transvection (ne_of_lt hij) t, root_mem hij t⟩ : borelSL F)⁆ =
      (⟨SpecialLinearGroup.transvection (ne_of_lt hij) (t * ((a : F)^2-1)), root_mem hij _⟩ : borelSL F) := by
  rw [commutatorElement_def, ← map_inv]
  apply Subtype.ext
  change diag2n (ne_of_lt hij) (a : F) a.ne_zero * SpecialLinearGroup.transvection (ne_of_lt hij) t *
    diag2n (ne_of_lt hij) ((a⁻¹ : Fˣ) : F) (a⁻¹).ne_zero * (SpecialLinearGroup.transvection (ne_of_lt hij) t)⁻¹ = _
  rw [transvection_inv]
  apply Subtype.ext
  fin_cases i <;> fin_cases j <;> simp only [Fin.lt_def] at hij <;> try omega
  all_goals
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [diag2n_coe, transvection_coe, Matrix.mul_apply, Fin.sum_univ_three,
        mul_assoc, pow_two]
  all_goals (ring_nf; simp [sub_eq_add_neg, add_comm])

variable [CharP F 2]

theorem borelSL_isPPerfect (hF : 2 < Nat.card F) : IsPPerfect 2 (borelSL F) := by
  classical
  let := Fintype.ofFinite F
  have hodd : Odd (Nat.card Fˣ) := by
    have heven : Even (Nat.card F) := by
      rw [Nat.card_eq_fintype_card]
      exact Nat.even_iff.mpr (FiniteField.even_card_of_char_two (ringChar.eq F 2))
    rw [Nat.card_units]
    exact Nat.Even.sub_odd (by omega) heven odd_one
  have hlarge : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  let : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hlarge
  obtain ⟨a, ha⟩ := exists_ne (1 : Fˣ)
  have ha1 : (a : F) ≠ 1 := fun h => ha (Units.ext h)
  have hasq : (a : F)^2 ≠ 1 := by
    intro h
    exact ha1 ((frobenius_inj F 2) (by simpa [frobenius_def] using h))
  intro N hN hQ
  let := hN
  let π := QuotientGroup.mk' N
  have hdiag {i j : Fin 3} (hij : i ≠ j) (b : Fˣ) : diagonalHom hij b ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    obtain ⟨k,hk⟩ := hQ (π (diagonalHom hij b))
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes (hodd.coprime_two_left.pow_left k)
    · exact orderOf_dvd_of_pow_eq_one hk
    · exact dvd_trans (orderOf_map_dvd (π.comp (diagonalHom hij)) b) (orderOf_dvd_natCard b)
  have hroot {i j : Fin 3} (hij : i < j) (t : F) :
      (⟨SpecialLinearGroup.transvection (ne_of_lt hij) t, root_mem hij t⟩ : borelSL F) ∈ N := by
    let v : borelSL F := ⟨SpecialLinearGroup.transvection (ne_of_lt hij) (t / ((a : F)^2-1)), root_mem hij _⟩
    have hc : ⁅diagonalHom (ne_of_lt hij) a, v⁆ ∈ N := by
      simpa only [commutatorElement_def, mul_assoc] using
        N.mul_mem (hdiag (ne_of_lt hij) a)
          (hN.conj_mem _ (N.inv_mem (hdiag (ne_of_lt hij) a)) v)
    have he := diagonal_commutator hij a (t / ((a : F)^2-1))
    rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hasq)] at he
    exact he ▸ hc
  have htorus (d : Fˣ × Fˣ) :
      (⟨torusSL F d, by rw [mem_borelSL_iff, torusSL_val]; simp⟩ : borelSL F) ∈ N := by
    have he : (⟨torusSL F d, by rw [mem_borelSL_iff, torusSL_val]; simp⟩ : borelSL F) =
        diagonalHom (i := 0) (j := 1) (by decide) d.1 *
          diagonalHom (i := 2) (j := 1) (by decide) d.2 := by
      apply Subtype.ext; apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [diagonalHom, diag2n_coe, torusSL_val, Matrix.mul_apply,
          Fin.sum_univ_three, mul_comm]
    rw [he]
    exact N.mul_mem (hdiag _ _) (hdiag _ _)
  apply top_unique
  intro g _
  obtain ⟨h10,h20,h21⟩ := (mem_borelSL_iff F g.val).mp g.property
  have hd : g.val.val 0 0 * g.val.val 1 1 * g.val.val 2 2 = 1 := by
    have h := g.val.property
    rw [Matrix.det_fin_three, h10,h20,h21] at h
    simpa only [zero_mul, mul_zero, add_zero, sub_zero] using h
  have h00 : g.val.val 0 0 ≠ 0 := by intro h; simp [h] at hd
  have h22 : g.val.val 2 2 ≠ 0 := by intro h; simp [h] at hd
  let d : Fˣ × Fˣ := (Units.mk0 _ h00, Units.mk0 _ h22)
  let u := g.val * torusSL F d⁻¹
  have hu : u ∈ unipotentSL F := by
    rw [unipotentSL, Subgroup.mem_inf, mem_pointLocalSL_iff, mem_lineLocalSL_iff]
    simp [u, torusSL_val, Matrix.mul_diagonal, d, h00,h22,h10,h20,h21]
  have hfactor : (⟨u, unipotentSL_le_borelSL F hu⟩ : borelSL F) =
      ⟨SpecialLinearGroup.transvection (i := 1) (j := 2) (by decide) (u.val 1 2), root_mem (by decide) _⟩ *
      ⟨SpecialLinearGroup.transvection (i := 0) (j := 2) (by decide) (u.val 0 2), root_mem (by decide) _⟩ *
      ⟨SpecialLinearGroup.transvection (i := 0) (j := 1) (by decide) (u.val 0 1), root_mem (by decide) _⟩ := by
    apply Subtype.ext; apply Subtype.ext
    rw [(mem_unipotentSL_iff F u).mp hu]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [transvection_coe, Matrix.mul_apply, Fin.sum_univ_three]
  have hun : (⟨u, unipotentSL_le_borelSL F hu⟩ : borelSL F) ∈ N := by
    rw [hfactor]
    exact N.mul_mem (N.mul_mem (hroot (by decide) _) (hroot (by decide) _)) (hroot (by decide) _)
  have hg : g = ⟨u, unipotentSL_le_borelSL F hu⟩ *
      ⟨torusSL F d, by rw [mem_borelSL_iff, torusSL_val]; simp⟩ := by
    apply Subtype.ext
    simp [u, map_inv, mul_assoc]
  rw [hg]
  exact N.mul_mem hun (htorus d)


/-- The two-residual uses quotients that are two-groups. -/
theorem borelSL_residual (hF : 2 < Nat.card F) : pResidual 2 (borelSL F) = ⊤ :=
  (pResidual_eq_top_iff _ _).mpr (borelSL_isPPerfect hF)

/-- Two-perfectness passes along the actual projection of Borels. -/
theorem borel_isPPerfect (hF : 2 < Nat.card F) : IsPPerfect 2 (borel F) :=
  (borelSL_isPPerfect hF).of_surjective ((projection F).subgroupMap (borelSL F))
    ((projection F).subgroupMap_surjective (borelSL F))

theorem borel_residual (hF : 2 < Nat.card F) : pResidual 2 (borel F) = ⊤ :=
  (pResidual_eq_top_iff _ _).mpr (borel_isPPerfect hF)

end Matrix.PSL3.HigherFieldBorelResidual
