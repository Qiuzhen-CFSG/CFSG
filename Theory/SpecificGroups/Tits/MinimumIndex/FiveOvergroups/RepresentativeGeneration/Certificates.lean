module

public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.RepresentativeGeneration.Data

/-!
# Kernel-checked recovery identities on the Atlas carrier

The packed permutations represent the same Atlas elements as the shared
representatives, the five-kernel generators, and the literal max4 generators.
The sixty recovery identities are checked at the certified three-point base;
faithfulness of that base turns the point checks into group equalities.
The exceptional max8 row uses its explicit conjugator, with convention
`g*x*g⁻¹`, exactly as in the consumer's subgroup map.

Source: the primary ATLAS max4 and max8 programs in `MinimumIndex/source/`.
The untrusted discovery witnesses and search are preserved in `source/`.
-/

namespace Tits.MinimumIndexFiveOvergroups.RepresentativeGeneration
open Subgroup FiveFrobenius MinimumIndexCandidates

private def fastLetter : Fin 4 → Equiv.Perm (Fin 1600) :=
  ![Packed.perm 0, Packed.perm 1, (Packed.perm 0)⁻¹, (Packed.perm 1)⁻¹]

private theorem fastLetter_eq (k : Fin 4) : fastLetter k = (letter k).val := by
  simp only [fastLetter, Packed.perm_eq]
  fin_cases k <;> rfl

private def fastRep8 (i : Fin 25) := ((max8Word i).map fastLetter).prod
private def fastRep4 (i : Fin 7) := ((max4Word i).map fastLetter).prod

private theorem fastWord_eq (w : List (Fin 4)) :
    (w.map fastLetter).prod = ((w.map letter).prod).val := by
  induction w with
  | nil => rfl
  | cons k w ih =>
    change fastLetter k * (w.map fastLetter).prod =
      (letter k).val * ((w.map letter).prod).val
    rw [fastLetter_eq, ih]

private theorem fastRep8_eq (i : Fin 25) : fastRep8 i = (max8Rep i).val := fastWord_eq _
private theorem fastRep4_eq (i : Fin 7) : fastRep4 i = (max4Rep i).val := fastWord_eq _

private def fastStandard : Fin 2 → Equiv.Perm (Fin 1600) := ![Packed.perm 0, Packed.perm 1]

private theorem fastStandard_eq (j : Fin 2) : fastStandard j = (standard j).val := by
  simp only [fastStandard, Packed.perm_eq]
  fin_cases j <;> rfl

private def fastMax4 : Equiv.Perm (Fin 1600) × Equiv.Perm (Fin 1600) :=
  let a := Packed.perm 0
  let b := Packed.perm 1
  let w0 := a * b
  let w1 := b * w0
  let w2 := w1 * a
  let w3 := w2⁻¹
  let w4 := a * w1
  let w5 := w3 * w4
  let w6 := w5 * w5
  let w7 := w0 * b
  let w8 := w0 * w7
  let w9 := w0 * w8
  let w10 := w9 ^ 3
  (w6, w10)

private theorem fastMax4_eq : fastMax4 = (max4Generators.1.val, max4Generators.2.val) := by
  simp only [fastMax4, Packed.perm_eq]
  rfl

private def fastPair (i : Fin 25) := pairInput (Packed.perm 2) (Packed.perm 3) (fastRep8 i)

private theorem pair_val (i : Fin 25) : (fun k => (pair i k).val) = fastPair i := by
  funext k
  simp only [fastPair, Packed.perm_eq, fastRep8_eq]
  fin_cases k
  · exact v_val
  · exact u_val
  · change (max8Rep i).val * v.val * (max8Rep i).val⁻¹ = _
    rw [v_val]; rfl
  · change (max8Rep i).val * u.val * (max8Rep i).val⁻¹ = _
    rw [u_val]; rfl

private def fastExtension (i : Fin 7) : Fin 3 → Equiv.Perm (Fin 1600) :=
  ![fastMax4.1, fastMax4.2, fastRep4 i]

private theorem extension_val (i : Fin 7) :
    (fun k => (extension i k).val) = fastExtension i := by
  funext k
  fin_cases k <;> simp only [fastExtension, fastMax4_eq, fastRep4_eq] <;> rfl

private def fastConjugator := eval fastStandard conjugatorWord

private theorem eval_val {n : Nat} (a : Fin n → Atlas1600Group) (w : List (Fin n × Bool)) :
    (eval a w).val = eval (fun k => (a k).val) w := by
  let f : Atlas1600Group →* Equiv.Perm (Fin 1600) := atlas1600Subgroup.subtype
  exact map_eval f a w

private theorem fastConjugator_eq : fastConjugator = exceptionalConjugator.val := by
  rw [exceptionalConjugator, eval_val]
  unfold fastConjugator
  congr 1
  funext k
  exact fastStandard_eq k

private def fastTarget8 (i : Fin 24) (j : Fin 2) : Equiv.Perm (Fin 1600) :=
  if i = 4 then fastConjugator * (![fastMax4.1, fastMax4.2] j) * fastConjugator⁻¹
  else fastStandard j

private theorem target8_val (i : Fin 24) (j : Fin 2) : (target8 i j).val = fastTarget8 i j := by
  by_cases hi : i = 4
  · simp only [target8, fastTarget8, hi, ↓reduceIte, fastConjugator_eq, fastMax4_eq]
    fin_cases j <;> rfl
  · simp only [target8, fastTarget8, hi, ↓reduceIte, fastStandard_eq]

set_option maxRecDepth 10000 in
private theorem checked8 : ∀ (i : Fin 24) (j : Fin 2) (p : Fin 3),
    eval (fastPair ⟨i.val + 1, by omega⟩) (recovery8 i j) ⟨p.val, by omega⟩ =
      (fastTarget8 i j) ⟨p.val, by omega⟩ := by
  apply Atlas1600OrderCertificate.allFin₃
  decide +kernel

set_option maxRecDepth 10000 in
private theorem checked4 : ∀ (i : Fin 6) (j : Fin 2) (p : Fin 3),
    eval (fastExtension ⟨i.val + 1, by omega⟩) (recovery4 i j) ⟨p.val, by omega⟩ =
      (fastStandard j) ⟨p.val, by omega⟩ := by
  apply Atlas1600OrderCertificate.allFin₃
  decide +kernel

/-- Recovery in the literal pair of conjugate five-kernels. -/
public theorem recovery8_eq (i : Fin 24) (j : Fin 2) :
    eval (pair ⟨i.val + 1, by omega⟩) (recovery8 i j) = target8 i j := by
  apply ConverseLocalCoverage.DoubleCosetCertificate.threePoint_ext
  all_goals rw [eval_val, pair_val, target8_val]
  · exact checked8 i j 0
  · exact checked8 i j 1
  · exact checked8 i j 2

/-- Recovery of the standard Atlas generators from max4 and a representative. -/
public theorem recovery4_eq (i : Fin 6) (j : Fin 2) :
    eval (extension ⟨i.val + 1, by omega⟩) (recovery4 i j) = standard j := by
  apply ConverseLocalCoverage.DoubleCosetCertificate.threePoint_ext
  all_goals rw [eval_val, extension_val, ← fastStandard_eq]
  · exact checked4 i j 0
  · exact checked4 i j 1
  · exact checked4 i j 2

end Tits.MinimumIndexFiveOvergroups.RepresentativeGeneration
