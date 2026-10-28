module
public import Theory.SpecificGroups.Thompson.TwoRankLower.Second
public import Theory.SpecificGroups.Thompson.TwoRankLower.Third
public import Theory.SpecificGroups.Thompson.TwoRankLower.Relations
public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.Tactic.FinCases

/-!
# An elementary eight in the actual Thompson carrier

Three powers of the actual max3 words are independent commuting involutions.
The bounded matrix certificates establish their relations in the faithful
248-dimensional representation. One off-diagonal matrix entry separates the
identity from each of the seven nonidentity products.
Source: ATLAS ThG1-max3W1; Aschbacher–Smith A.2.12, printed p.36.
-/
public noncomputable section
namespace Thompson.TwoRank
open Matrices
private def generatorRows : Fin 3 → Rows := ![a,b,c]
private theorem exists_generators (i : Fin 3) :
    ∃ g : Model, matrixHom g = BinaryMatrix.decode 248 (generatorRows i) := by
  fin_cases i
  · exact witness_a
  · exact witness_b
  · exact witness_c
private def generators (i : Fin 3) : Model := (exists_generators i).choose
private theorem representation_generators (i : Fin 3) :
    matrixHom (generators i) = BinaryMatrix.decode 248 (generatorRows i) :=
  (exists_generators i).choose_spec
private theorem generators_square (i : Fin 3) : generators i ^ 2 = 1 := by
  apply matrixHom_injective
  rw [map_pow,map_one,representation_generators,pow_two]
  fin_cases i
  · exact rel_aa.trans decode_unit
  · exact rel_bb.trans decode_unit
  · exact rel_cc.trans decode_unit
private theorem generators_commute (i j : Fin 3) : Commute (generators i) (generators j) := by
  apply matrixHom_injective
  simp only [map_mul,representation_generators]
  fin_cases i <;> fin_cases j
  · rfl
  · exact rel_ab.trans rel_ba.symm
  · exact rel_ac.trans rel_ca.symm
  · exact rel_ba.trans rel_ab.symm
  · rfl
  · exact rel_bc.trans rel_cb.symm
  · exact rel_ca.trans rel_ac.symm
  · exact rel_cb.trans rel_bc.symm
  · rfl
private def cycle (i : Fin 3) : Multiplicative (ZMod 2) →* Model where
  toFun a := generators i ^ a.toAdd.val
  map_one' := pow_zero _
  map_mul' a b := by
    change generators i ^ (a.toAdd+b.toAdd).val = _
    rw [ZMod.val_add,← pow_add]
    exact pow_eq_pow_of_modEq (Nat.mod_mod _ _) (generators_square i)
private theorem cycles_commute : Pairwise (fun (i j : Fin 3) =>
    ∀ (a b : Multiplicative (ZMod 2)), Commute (cycle i a) (cycle j b)) := by
  intro i j _ a b
  change Commute (generators i ^ a.toAdd.val) (generators j ^ b.toAdd.val)
  exact @Commute.pow_pow Model (inferInstance : Monoid Model)
    (generators i) (generators j) (generators_commute i j) a.toAdd.val b.toAdd.val
/-- An actual elementary abelian subgroup of the Thompson carrier. -/
def embedding : (Fin 3 → Multiplicative (ZMod 2)) →* Model :=
  MonoidHom.noncommPiCoprod cycle cycles_commute
private theorem embedding_apply (v : Fin 3 → Multiplicative (ZMod 2)) :
    embedding v = generators 0 ^ (v 0).toAdd.val *
      (generators 1 ^ (v 1).toAdd.val * generators 2 ^ (v 2).toAdd.val) := by
  rw [embedding,MonoidHom.noncommPiCoprod_apply]
  have h : (Finset.univ : Finset (Fin 3)) = [0,1,2].toFinset := by decide
  rw [h,Finset.noncommProd_toFinset _ _ _ (by decide)]
  simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
  rfl
private def wordRows (v w z : ZMod 2) : Rows :=
  if v=0 then if w=0 then if z=0 then unit else c else if z=0 then b else bc
  else if w=0 then if z=0 then a else ac else if z=0 then ab else abc
private theorem matrix_word (v w z : ZMod 2) :
    BinaryMatrix.decode 248 a ^ v.val *
      (BinaryMatrix.decode 248 b ^ w.val * BinaryMatrix.decode 248 c ^ z.val) =
      BinaryMatrix.decode 248 (wordRows v w z) := by
  fin_cases v <;> fin_cases w <;> fin_cases z
  · change BinaryMatrix.decode 248 a ^ 0 * (BinaryMatrix.decode 248 b ^ 0 * BinaryMatrix.decode 248 c ^ 0) = BinaryMatrix.decode 248 unit
    simpa only [pow_zero,mul_one] using decode_unit.symm
  · change BinaryMatrix.decode 248 a ^ 0 * (BinaryMatrix.decode 248 b ^ 0 * BinaryMatrix.decode 248 c ^ 1) = BinaryMatrix.decode 248 c
    simp only [pow_zero,pow_one,one_mul]
  · change BinaryMatrix.decode 248 a ^ 0 * (BinaryMatrix.decode 248 b ^ 1 * BinaryMatrix.decode 248 c ^ 0) = BinaryMatrix.decode 248 b
    simp only [pow_zero,pow_one,mul_one,one_mul]
  · change BinaryMatrix.decode 248 a ^ 0 * (BinaryMatrix.decode 248 b ^ 1 * BinaryMatrix.decode 248 c ^ 1) = BinaryMatrix.decode 248 bc
    simpa only [pow_zero,pow_one,one_mul] using rel_bc
  · change BinaryMatrix.decode 248 a ^ 1 * (BinaryMatrix.decode 248 b ^ 0 * BinaryMatrix.decode 248 c ^ 0) = BinaryMatrix.decode 248 a
    simp only [pow_zero,pow_one,mul_one]
  · change BinaryMatrix.decode 248 a ^ 1 * (BinaryMatrix.decode 248 b ^ 0 * BinaryMatrix.decode 248 c ^ 1) = BinaryMatrix.decode 248 ac
    simpa only [pow_zero,pow_one,one_mul] using rel_ac
  · change BinaryMatrix.decode 248 a ^ 1 * (BinaryMatrix.decode 248 b ^ 1 * BinaryMatrix.decode 248 c ^ 0) = BinaryMatrix.decode 248 ab
    simpa only [pow_zero,pow_one,mul_one] using rel_ab
  · change BinaryMatrix.decode 248 a ^ 1 * (BinaryMatrix.decode 248 b ^ 1 * BinaryMatrix.decode 248 c ^ 1) = BinaryMatrix.decode 248 abc
    simp only [pow_one,← mul_assoc,rel_ab,rel_abc]
private theorem representation_embedding (v : Fin 3 → Multiplicative (ZMod 2)) :
    matrixHom (embedding v) =
      BinaryMatrix.decode 248 (wordRows (v 0).toAdd (v 1).toAdd (v 2).toAdd) := by
  rw [embedding_apply]
  simp only [map_mul,map_pow,representation_generators]
  exact matrix_word _ _ _
private theorem wordRows_kernel : ∀ v w z : ZMod 2,
    BinaryMatrix.decode 248 (wordRows v w z) 0 108 = 0 →
      v=0 ∧ w=0 ∧ z=0 := by decide +kernel
/-- Independence is checked in the faithful representation. -/
theorem embedding_injective : Function.Injective embedding := by
  apply (injective_iff_map_eq_one embedding).mpr
  intro v hv
  have h := congrArg matrixHom hv
  rw [representation_embedding,map_one] at h
  obtain ⟨h0,h1,h2⟩ := wordRows_kernel _ _ _ (congrArg (fun m => m 0 108) h)
  funext i
  apply Multiplicative.toAdd.injective
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
/-- The actual Thompson carrier has two-rank at least three. -/
theorem three_le_twoRank : 3 ≤ primeRank 2 Model := by
  apply primeRank_ge_of_elementary_embedding (f := embedding) (hf := embedding_injective)
  · intro v
    funext i
    change Multiplicative.ofAdd (2 • (v i).toAdd) = Multiplicative.ofAdd 0
    exact congrArg Multiplicative.ofAdd (ZModModule.char_nsmul_eq_zero 2 (v i).toAdd)
  · simp [Nat.card_eq_fintype_card]
end Thompson.TwoRank
