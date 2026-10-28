module

public import Theory.SpecificGroups.PSL3.OuterSolvable.OddPrimeCoverage.RootRigidity
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Perfect

/-!
# The field part cannot be ignored in a root-centralizer calculation

On the actual highest-root matrices of PSL₃, conjugation by diag(1,b,1)
acts trivially, so its product with a field automorphism acts by that field
automorphism. It fixes x₀₂(1) without fixing the entire root group whenever
the field automorphism is nontrivial. Over a field of order 64 the diagonal
parameter can be chosen noncubic and the field action is t ↦ t⁴.

These are coordinate diagnostics for the nonsplit alternative in
Aschbacher–Smith A.3.16–18 and the proposed uniform calculation on p.927.
They do not identify the entire nonsplit extension or realize it in the
ambient chapter configuration. In that configuration the independent
identity Lᵥ = [Lᵥ,Tᵥ] may exclude the field part; that requires a further
compatible quotient-action argument.
-/

@[expose] public section
open scoped MatrixGroups
open Matrix
open Matrix.PSL3.OuterSolvable Matrix.PSL3.OuterSolvable.OddPrimeCoverage
namespace Matrix.PSL3.NormalizedRootCentralizers
variable {F : Type*} [Field F]

private theorem field_root (σ : F ≃+* F) {i j : Fin 3} (hij : i ≠ j) (a : F) :
    fieldAction F σ (rootElement hij a) = rootElement hij (σ a) := by
  rw [rootElement, fieldAction_mk]
  congr 1
  apply Subtype.ext
  ext k l
  change σ ((1 + Matrix.single i j a) k l) = (1 + Matrix.single i j (σ a)) k l
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, map_add]
  split_ifs <;> simp

/-- The diagonal-field actor on the genuine projective matrix group. -/
def middleField (b : Fˣ) (σ : F ≃+* F) : MulAut PSL(3,F) :=
  linearConj F (diagonalGL ![1, b, 1]) * fieldAction F σ

theorem middleField_root (b : Fˣ) (σ : F ≃+* F) (a : F) :
    middleField b σ (rootElement (by decide : (0 : Fin 3) ≠ 2) a) =
      rootElement (by decide : (0 : Fin 3) ≠ 2) (σ a) := by
  simp [middleField, MulAut.mul_apply, field_root, linearConj_diagonalGL_rootElement]

theorem middleField_fixes_one (b : Fˣ) (σ : F ≃+* F) :
    middleField b σ (rootElement (by decide : (0 : Fin 3) ≠ 2) 1) =
      rootElement (by decide : (0 : Fin 3) ≠ 2) 1 := by
  rw [middleField_root, map_one]

/-- Pointwise fixation of the highest root detects the entire field part. -/
theorem middleField_fixes_root_iff (b : Fˣ) (σ : F ≃+* F) :
    (∀ r ∈ rootGroup (F := F) (by decide : (0 : Fin 3) ≠ 2), middleField b σ r = r) ↔
      σ = RingEquiv.refl F := by
  constructor
  · intro h
    ext a
    apply rootElement_injective (by decide : (0 : Fin 3) ≠ 2)
    rw [← middleField_root]
    exact h _ (rootElement_mem _ a)
  · rintro rfl r ⟨a, rfl⟩
    exact middleField_root b (RingEquiv.refl F) a.toAdd

/-- A noncubic diagonal parameter does not repair the field obstruction.
This is the first allowed linear nonsplit parameter q = 2⁶. -/
theorem field64_noncubic_actor [Finite F] [CharP F 2] (hF : Nat.card F = 64) :
    ∃ b : Fˣ, (¬ ∃ c : Fˣ, c ^ 3 = b) ∧
      middleField b (iterateFrobeniusEquiv F 2 2)
        (rootElement (by decide : (0 : Fin 3) ≠ 2) 1) =
          rootElement (by decide : (0 : Fin 3) ≠ 2) 1 ∧
      rootElement (by decide : (0 : Fin 3) ≠ 2) (b : F) ≠ 1 ∧
      middleField b (iterateFrobeniusEquiv F 2 2)
        (rootElement (by decide : (0 : Fin 3) ≠ 2) (b : F)) ≠
          rootElement (by decide : (0 : Fin 3) ≠ 2) (b : F) := by
  obtain ⟨b, hb⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hcard : Nat.card Fˣ = 63 := by rw [Nat.card_units, hF]
  rw [hcard] at hb
  refine ⟨b, ?_, middleField_fixes_one b _, ?_, ?_⟩
  · rintro ⟨c, hc⟩
    have he : b ^ 21 = 1 := by
      rw [← hc, ← pow_mul]
      simpa only [hcard] using (pow_card_eq_one' (x := c))
    have hd := orderOf_dvd_iff_pow_eq_one.mpr he
    rw [hb] at hd
    norm_num at hd
  · exact fun he => b.ne_zero ((rootElement_eq_one_iff _ _).mp he)
  · intro he
    rw [middleField_root] at he
    have hf := rootElement_injective (by decide : (0 : Fin 3) ≠ 2) he
    rw [iterateFrobeniusEquiv_def] at hf
    have hb4 : b ^ 4 = b := Units.ext hf
    have hb3 : b ^ 3 = 1 := by
      apply mul_right_cancel (b := b)
      simpa only [← pow_succ, one_mul] using hb4
    have hd := orderOf_dvd_iff_pow_eq_one.mpr hb3
    rw [hb] at hd
    norm_num at hd

end Matrix.PSL3.NormalizedRootCentralizers
