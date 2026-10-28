module
public import Theory.SpecificGroups.Lyons.TwoRankLower.Second
public import Theory.SpecificGroups.Lyons.TwoRankLower.Relations
public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.Tactic.FinCases

/-!
# An elementary eight in the actual Lyons carrier

Three powers of the actual max4 words are independent commuting involutions.
The bounded matrix certificates establish their relations in the faithful
111-dimensional representation. One off-diagonal matrix entry separates the
identity from each of the seven nonidentity products.
Source: ATLAS LyG1-max4W1; Aschbacher–Smith A.2.12, printed p.36.
-/
public noncomputable section
namespace Lyons.TwoRank
open Matrices
private def generatorRows : Fin 3 → Rows := ![a,b,t]
private theorem exists_generators (i : Fin 3) :
    ∃ g : LyonsGroup, matrixRepresentation g = Atlas111WordCertificate.decode (generatorRows i) := by
  fin_cases i
  · exact witness_a
  · exact witness_b
  · exact witness_t
private def generators (i : Fin 3) : LyonsGroup := (exists_generators i).choose
private theorem representation_generators (i : Fin 3) :
    matrixRepresentation (generators i) = Atlas111WordCertificate.decode (generatorRows i) :=
  (exists_generators i).choose_spec
private theorem generators_square (i : Fin 3) : generators i ^ 2 = 1 := by
  apply matrixRepresentation_injective
  rw [map_pow,map_one,representation_generators,pow_two]
  fin_cases i
  · exact rel_aa.trans decode_unit
  · exact rel_bb.trans decode_unit
  · exact rel_tt.trans decode_unit
private theorem generators_commute (i j : Fin 3) : Commute (generators i) (generators j) := by
  apply matrixRepresentation_injective
  simp only [map_mul,representation_generators]
  fin_cases i <;> fin_cases j
  · rfl
  · exact rel_ab.trans rel_ba.symm
  · exact rel_at.trans rel_ta.symm
  · exact rel_ba.trans rel_ab.symm
  · rfl
  · exact rel_bt.trans rel_tb.symm
  · exact rel_ta.trans rel_at.symm
  · exact rel_tb.trans rel_bt.symm
  · rfl
private def cycle (i : Fin 3) : Multiplicative (ZMod 2) →* LyonsGroup where
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
  exact @Commute.pow_pow LyonsGroup (inferInstance : Monoid LyonsGroup)
    (generators i) (generators j) (generators_commute i j) a.toAdd.val b.toAdd.val
/-- An actual elementary abelian subgroup of the Lyons carrier. -/
def embedding : (Fin 3 → Multiplicative (ZMod 2)) →* LyonsGroup :=
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
  if v=0 then if w=0 then if z=0 then unit else t else if z=0 then b else bc
  else if w=0 then if z=0 then a else ac else if z=0 then ab else abc
private theorem matrix_word (v w z : ZMod 2) :
    Atlas111WordCertificate.decode a ^ v.val *
      (Atlas111WordCertificate.decode b ^ w.val * Atlas111WordCertificate.decode t ^ z.val) =
      Atlas111WordCertificate.decode (wordRows v w z) := by
  fin_cases v <;> fin_cases w <;> fin_cases z
  · change Atlas111WordCertificate.decode a ^ 0 * (Atlas111WordCertificate.decode b ^ 0 * Atlas111WordCertificate.decode t ^ 0) = Atlas111WordCertificate.decode unit
    simpa only [pow_zero,mul_one] using decode_unit.symm
  · change Atlas111WordCertificate.decode a ^ 0 * (Atlas111WordCertificate.decode b ^ 0 * Atlas111WordCertificate.decode t ^ 1) = Atlas111WordCertificate.decode t
    simp only [pow_zero,pow_one,one_mul]
  · change Atlas111WordCertificate.decode a ^ 0 * (Atlas111WordCertificate.decode b ^ 1 * Atlas111WordCertificate.decode t ^ 0) = Atlas111WordCertificate.decode b
    simp only [pow_zero,pow_one,mul_one,one_mul]
  · change Atlas111WordCertificate.decode a ^ 0 * (Atlas111WordCertificate.decode b ^ 1 * Atlas111WordCertificate.decode t ^ 1) = Atlas111WordCertificate.decode bc
    simpa only [pow_zero,pow_one,one_mul] using rel_bt
  · change Atlas111WordCertificate.decode a ^ 1 * (Atlas111WordCertificate.decode b ^ 0 * Atlas111WordCertificate.decode t ^ 0) = Atlas111WordCertificate.decode a
    simp only [pow_zero,pow_one,mul_one]
  · change Atlas111WordCertificate.decode a ^ 1 * (Atlas111WordCertificate.decode b ^ 0 * Atlas111WordCertificate.decode t ^ 1) = Atlas111WordCertificate.decode ac
    simpa only [pow_zero,pow_one,one_mul] using rel_at
  · change Atlas111WordCertificate.decode a ^ 1 * (Atlas111WordCertificate.decode b ^ 1 * Atlas111WordCertificate.decode t ^ 0) = Atlas111WordCertificate.decode ab
    simpa only [pow_zero,pow_one,mul_one] using rel_ab
  · change Atlas111WordCertificate.decode a ^ 1 * (Atlas111WordCertificate.decode b ^ 1 * Atlas111WordCertificate.decode t ^ 1) = Atlas111WordCertificate.decode abc
    simp only [pow_one,← mul_assoc,rel_ab,rel_abt]
private theorem representation_embedding (v : Fin 3 → Multiplicative (ZMod 2)) :
    matrixRepresentation (embedding v) =
      Atlas111WordCertificate.decode (wordRows (v 0).toAdd (v 1).toAdd (v 2).toAdd) := by
  rw [embedding_apply]
  simp only [map_mul,map_pow,representation_generators]
  exact matrix_word _ _ _
private theorem wordRows_kernel : ∀ v w z : ZMod 2,
    Atlas111WordCertificate.decode (wordRows v w z) 0 3 = 0 →
      v=0 ∧ w=0 ∧ z=0 := by decide +kernel
/-- Independence is checked in the faithful representation. -/
theorem embedding_injective : Function.Injective embedding := by
  apply (injective_iff_map_eq_one embedding).mpr
  intro v hv
  have h := congrArg matrixRepresentation hv
  rw [representation_embedding,map_one] at h
  obtain ⟨h0,h1,h2⟩ := wordRows_kernel _ _ _ (congrArg (fun m => m 0 3) h)
  funext i
  apply Multiplicative.toAdd.injective
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
/-- The actual Lyons carrier has two-rank at least three. -/
theorem three_le_twoRank : 3 ≤ primeRank 2 LyonsGroup := by
  apply primeRank_ge_of_elementary_embedding (f := embedding) (hf := embedding_injective)
  · intro v
    funext i
    change Multiplicative.ofAdd (2 • (v i).toAdd) = Multiplicative.ofAdd 0
    exact congrArg Multiplicative.ofAdd (ZModModule.char_nsmul_eq_zero 2 (v i).toAdd)
  · simp [Nat.card_eq_fintype_card]
end Lyons.TwoRank
