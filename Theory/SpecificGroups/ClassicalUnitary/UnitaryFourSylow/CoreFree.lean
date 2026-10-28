module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.Normalizer
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourGeneration

/-!
# Trivial normal core of the unitary-four flag stabilizer

A normal subgroup contained in the coordinate flag stabilizer consists of
upper triangular matrices. Conjugation by coordinate reversal makes them
lower triangular too, hence diagonal. Two point-radical matrices force all
four diagonal entries to coincide. The determinant-one condition and
injectivity of the fourth-power Frobenius then force the identity.

This proves the normal-core condition in Aschbacher--Smith Definition F.1.7,
printed p.261, for the U₄(q) amalgam of F.1.12(I)(6), printed p.263 of
`refs/quasithin.pdf`. It does not require a simplicity theorem and includes q=2.
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPointLocal UnitaryFourGeneration
public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow
variable (F : Type*) [Field F] [CharP F 2] [Finite F]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "B" => borelSU F (form F σ hσ)

private theorem normal_mem_diagonal (N : Subgroup (SU F (form F σ hσ)))
    [N.Normal] (hN : N ≤ B) (a : SU F (form F σ hσ)) (ha : a ∈ N) :
    a.val.val = Matrix.diagonal (fun i => a.val.val i i) := by
  let w := reverse F σ hσ
  have hw : w * w = 1 := by
    apply Subtype.ext
    apply Units.ext
    change w.val.val * w.val.val = 1
    rw [reverse_val, gram_sq]
  have hwi : w⁻¹ = w := (inv_eq_iff_mul_eq_one).mpr hw
  have hwaw : w * a * w ∈ N := by
    simpa only [hwi] using Subgroup.Normal.conj_mem (inferInstance : N.Normal) a ha w
  have ht := (mem_borel_iff_triangular F σ hσ a).mp (hN ha)
  have ht' := (mem_borel_iff_triangular F σ hσ (w*a*w)).mp (hN hwaw)
  have h23 := ht' (by decide : (0 : Fin 4) < 1)
  have h13 := ht' (by decide : (0 : Fin 4) < 2)
  have h03 := ht' (by decide : (0 : Fin 4) < 3)
  have h12 := ht' (by decide : (1 : Fin 4) < 2)
  have h02 := ht' (by decide : (1 : Fin 4) < 3)
  have h01 := ht' (by decide : (2 : Fin 4) < 3)
  change (w.val.val * a.val.val * w.val.val) 1 0 = 0 at h23
  change (w.val.val * a.val.val * w.val.val) 2 0 = 0 at h13
  change (w.val.val * a.val.val * w.val.val) 3 0 = 0 at h03
  change (w.val.val * a.val.val * w.val.val) 2 1 = 0 at h12
  change (w.val.val * a.val.val * w.val.val) 3 1 = 0 at h02
  change (w.val.val * a.val.val * w.val.val) 3 2 = 0 at h01
  simp [w, reverse_val, gram, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
    at h23 h13 h03 h12 h02 h01
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · rw [Matrix.diagonal_apply_ne _ hij]
    rcases lt_or_gt_of_ne hij with h | h
    · fin_cases i <;> fin_cases j <;> simp_all
    · exact ht h

/-- A normal subgroup of SU₄ contained in the whole flag stabilizer is trivial. -/
theorem eq_bot_of_normal_le_borel (N : Subgroup (SU F (form F σ hσ)))
    [N.Normal] (hN : N ≤ B) : N = ⊥ := by
  apply le_antisymm _ bot_le
  intro a ha
  have had := normal_mem_diagonal F σ hσ N hN a ha
  have hconj (c : RadicalCoordinates F σ) :
      ∀ i j : Fin 4,
        (radicalMatrix F σ c) i j * a.val.val j j =
          a.val.val i i * (radicalMatrix F σ c) i j := by
    let r := radicalElement F σ hσ c
    let b := r * a * r⁻¹
    have hb : b ∈ N := Subgroup.Normal.conj_mem inferInstance a ha r
    have hbd := normal_mem_diagonal F σ hσ N hN b hb
    have he : r * a = b * r := by dsimp [b]; group
    have he' : r.val.val * a.val.val = b.val.val * r.val.val :=
      congrArg (fun x : SU F (form F σ hσ) => x.val.val) he
    rw [had, hbd] at he'
    have hbdiag (i : Fin 4) : b.val.val i i = a.val.val i i := by
      have hi := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M i i) he'
      simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at hi
      have hri : r.val.val i i = 1 := by
        dsimp [r, radicalElement, radicalMatrix]
        fin_cases i <;> rfl
      simpa [hri] using hi.symm
    intro i j
    have hij := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M i j) he'
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, hbdiag] at hij
    exact hij
  let cx : RadicalCoordinates F σ := ⟨1,0,0, by simp⟩
  let cy : RadicalCoordinates F σ := ⟨0,1,0, by simp⟩
  have h20 : a.val.val 2 2 = a.val.val 0 0 := by
    simpa [radicalMatrix,cx] using hconj cx 0 2
  have h10 : a.val.val 1 1 = a.val.val 0 0 := by
    simpa [radicalMatrix,cy] using hconj cy 0 1
  have h31 : a.val.val 3 3 = a.val.val 1 1 := by
    simpa [radicalMatrix,cx] using hconj cx 1 3
  have hd : a.val.val.det = 1 := congrArg Units.val a.property.2
  rw [had, Matrix.det_diagonal] at hd
  have hp : a.val.val 0 0 ^ 4 = 1 := by
    simpa [Fin.prod_univ_succ,h20,h10,h31,pow_succ,mul_assoc] using hd
  have h0 : a.val.val 0 0 = 1 := (iterateFrobeniusEquiv F 2 2).injective (by
    change a.val.val 0 0 ^ (2 ^ 2) = (1 : F) ^ (2 ^ 2)
    simpa using hp)
  change a = 1
  apply Subtype.ext
  apply Units.ext
  change a.val.val = 1
  rw [had]
  have he : (fun i => a.val.val i i) = fun _ => (1 : F) := by
    funext i
    fin_cases i <;> simp [h0,h10,h20,h31]
  rw [he, Matrix.diagonal_one]

/-- The faithful-completion core condition for the literal flag amalgam. -/
theorem borel_normalCore_eq_bot : (B).normalCore = ⊥ :=
  eq_bot_of_normal_le_borel F σ hσ _ (B).normalCore_le

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow
