module

public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.Tactic.FinCases

/-!
# Defining-characteristic witnesses in PSL₄

The first-row unipotent matrices form a copy of the additive group of F³.
Their three off-diagonal entries vanish if such a matrix is scalar, so this
copy survives the central quotient. Over |F| = p^e it witnesses rank at
least 3e. No restriction on the characteristic is needed.

Source application: Aschbacher–Smith, *The Classification of Quasithin
Groups*, combined manuscript (1 March 2004), A.2.17, printed p.39.
-/

@[expose] public section

open Matrix
open scoped MatrixGroups
namespace Matrix.PSL4.DefiningRank
variable (F : Type*) [Field F]

def rowFour (v : Fin 3 → F) : SL(4,F) :=
  ⟨!![1,v 0,v 1,v 2; 0,1,0,0; 0,0,1,0; 0,0,0,1], by
    simp [Matrix.det_succ_column_zero, Fin.sum_univ_succ]⟩

def rowFourHom : Multiplicative (Fin 3 → F) →* SL(4,F) where
  toFun v := rowFour F v.toAdd
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rowFour]
  map_mul' v w := by
    apply Subtype.ext
    change (rowFour F (v.toAdd + w.toAdd)).val = (rowFour F v.toAdd).val * (rowFour F w.toAdd).val
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rowFour, Matrix.mul_apply, Fin.sum_univ_succ, add_comm]

def projectiveRowFour : Multiplicative (Fin 3 → F) →* PSL(4,F) :=
  (QuotientGroup.mk' _).comp (rowFourHom F)

theorem projectiveRowFour_injective : Function.Injective (projectiveRowFour F) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro v hv
  have hc : rowFour F v.toAdd ∈ Subgroup.center SL(4,F) :=
    (QuotientGroup.eq_one_iff _).mp hv
  obtain ⟨c, _, hc⟩ := SpecialLinearGroup.mem_center_iff.mp hc
  change v.toAdd = 0
  funext i
  have he := congrArg (fun m : Matrix (Fin 4) (Fin 4) F => m 0 i.succ) hc
  fin_cases i <;> simpa [rowFour, Matrix.scalar_apply, Matrix.diagonal_apply] using he.symm

theorem three_mul_fieldExponent_le_primeRank [Finite F] {p e : ℕ} [Fact p.Prime] [CharP F p]
    (hc : Nat.card F = p ^ e) : 3 * e ≤ primeRank p PSL(4,F) := by
  refine primeRank_ge_of_elementary_embedding (A := Multiplicative (Fin 3 → F))
    ?_ ?_ (projectiveRowFour F) (projectiveRowFour_injective F)
  · intro v
    change p • v.toAdd = 0
    ext i
    simp [nsmul_eq_mul]
  · change Nat.card (Fin 3 → F) = _
    rw [Nat.card_fun, Nat.card_fin, hc, ← pow_mul, Nat.mul_comm e 3]


end Matrix.PSL4.DefiningRank
