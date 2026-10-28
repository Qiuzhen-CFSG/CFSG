module

public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.Extension
public import Theory.GroupTheory.PrimeRankWitness

/-!
# Symmetric-shear witnesses in PSp₄

The shears with a symmetric two-by-two upper-right block contain the
additive group F³. A shear in the center commutes with the standard
symplectic matrix; comparison of their upper-left blocks makes the shear
trivial. Consequently this additive group embeds in the literal quotient
Sp₄/Z(Sp₄), giving defining prime rank at least 3e over |F| = p^e.

Source application: Aschbacher–Smith, *The Classification of Quasithin
Groups*, A.2.17, printed p.39. The construction also works in characteristic two.
-/

@[expose] public section

open Matrix
namespace Theory.SpecificGroups.SymplecticFour.DefiningRank
open Theory.SpecificGroups.SymplecticFour.Plane
variable (F : Type*) [Field F]

def symParameters (v : Fin 3 → F) : symmetricMatrices F :=
  ⟨!![v 0, v 1; v 1, v 2], by ext i j; fin_cases i <;> fin_cases j <;> rfl⟩

def symShearHom : Multiplicative (Fin 3 → F) →* Matrix.symplecticGroup (Fin 2) F where
  toFun v := shearSp (symParameters F v.toAdd)
  map_one' := by
    have hz : symParameters F (0 : Fin 3 → F) = 0 := by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    apply Subtype.ext
    change (shearSp (symParameters F (0 : Fin 3 → F))).val = _
    rw [hz]
    exact fromBlocks_one
  map_mul' v w := by
    apply Subtype.ext
    change fromBlocks 1 _ 0 1 = fromBlocks 1 _ 0 1 * fromBlocks 1 _ 0 1
    simp only [fromBlocks_multiply, one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [symParameters, add_comm]

def projectiveSymShear : Multiplicative (Fin 3 → F) →*
    (Matrix.symplecticGroup (Fin 2) F ⧸ Subgroup.center (Matrix.symplecticGroup (Fin 2) F)) :=
  (QuotientGroup.mk' _).comp (symShearHom F)

theorem projectiveSymShear_injective : Function.Injective (projectiveSymShear F) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro v hv
  have hc : symShearHom F v ∈ Subgroup.center (Matrix.symplecticGroup (Fin 2) F) :=
    (QuotientGroup.eq_one_iff _).mp hv
  have he := Subgroup.mem_center_iff.mp hc (SymplecticGroup.symJ (Fin 2) F)
  have hm := congrArg Subtype.val he
  change fromBlocks 0 (-1) 1 0 * fromBlocks 1 (symParameters F v.toAdd).val 0 1 =
    fromBlocks 1 (symParameters F v.toAdd).val 0 1 * fromBlocks 0 (-1) 1 0 at hm
  simp only [fromBlocks_multiply, one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add] at hm
  have hz : (symParameters F v.toAdd).val = 0 := (fromBlocks_inj.mp hm).1.symm
  change v.toAdd = 0
  funext i
  fin_cases i
  · exact congrArg (fun m : Matrix (Fin 2) (Fin 2) F => m 0 0) hz
  · exact congrArg (fun m : Matrix (Fin 2) (Fin 2) F => m 0 1) hz
  · exact congrArg (fun m : Matrix (Fin 2) (Fin 2) F => m 1 1) hz

theorem three_mul_fieldExponent_le_primeRank [Finite F] {p e : ℕ} [Fact p.Prime] [CharP F p]
    (hc : Nat.card F = p ^ e) :
    3 * e ≤ primeRank p (Matrix.symplecticGroup (Fin 2) F ⧸
      Subgroup.center (Matrix.symplecticGroup (Fin 2) F)) := by
  refine primeRank_ge_of_elementary_embedding (A := Multiplicative (Fin 3 → F))
    ?_ ?_ (projectiveSymShear F) (projectiveSymShear_injective F)
  · intro v
    change p • v.toAdd = 0
    ext i
    simp [nsmul_eq_mul]
  · change Nat.card (Fin 3 → F) = _
    rw [Nat.card_fun, Nat.card_fin, hc, ← pow_mul, Nat.mul_comm e 3]
end Theory.SpecificGroups.SymplecticFour.DefiningRank
