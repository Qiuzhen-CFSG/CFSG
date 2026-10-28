module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.Degree21.SmallDegrees.Arithmetic.Triples

/-!
# Passing from Gram norms to distinct constituent indices

Unit coefficients identify each nonprincipal support's cardinality with its
Gram norm minus the principal contribution. The first three supports therefore
have three distinct indices. Their degree, Gram, and Suzuki sums give precisely
the signed equations consumed by the finite certificates.
Source: Janko (1968), Sections 6--7.
-/

open scoped BigOperators
namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21.SmallDegrees.Arithmetic
open CharacterOrder
variable {J : Type*} [Fintype J] (S : DegreeSystem J)

public theorem degree_le (j : J) : S.degree j ≤ 665 := by
  have h := Finset.single_le_sum (f := fun j => S.degree j ^ 2)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  rw [S.sum_squares] at h
  nlinarith

noncomputable section
attribute [local instance] Classical.decEq
@[expose] public def support (i : Fin 5) : Finset J := by
  classical
  exact (Finset.univ.erase S.principal).filter (fun j => S.coefficient i j ≠ 0)

public theorem mem_support (i : Fin 5) (j : J) :
    j ∈ support S i ↔ j ≠ S.principal ∧ S.coefficient i j ≠ 0 := by
  classical
  simp [support]

public theorem sum_support {A : Type*} [AddCommGroup A] (i : Fin 5)
    (f : J → A) (hf : ∀ j, S.coefficient i j = 0 → f j = 0) :
    (∑ j ∈ support S i, f j) + f S.principal = ∑ j, f j := by
  classical
  have he : (∑ j ∈ support S i, f j) = ∑ j ∈ Finset.univ.erase S.principal, f j := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j hj hn
    exact hf j (by simpa [support, hj] using hn)
  rw [he, Finset.sum_erase_add _ _ (Finset.mem_univ _)]

public theorem support_card_three (i : Fin 3) : (support S (i.castLE (by decide))).card = 3 := by
  classical
  let k : Fin 5 := i.castLE (by decide)
  have he := sum_support S k (fun j => S.coefficient k j * S.coefficient k j)
    (by intro j hj; simp [hj])
  have hs : (∑ j ∈ support S k, S.coefficient k j * S.coefficient k j) =
      ((support S k).card : ℤ) := by
    calc
      _ = ∑ _j ∈ support S k, (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hn := ((mem_support S k j).mp hj).2
        rcases S.unit k j with h | h | h <;> simp_all
      _ = _ := by simp
  rw [hs, S.gram, S.principal_coefficient] at he
  dsimp [k] at he ⊢
  fin_cases i <;> simp [Fin.castLE, exceptionalCoefficients, exceptionalGram] at he ⊢ <;> omega

public theorem support_card_five : (support S 4).card = 5 := by
  classical
  have he := sum_support S 4 (fun j => S.coefficient 4 j * S.coefficient 4 j)
    (by intro j hj; simp [hj])
  have hs : (∑ j ∈ support S 4, S.coefficient 4 j * S.coefficient 4 j) =
      ((support S 4).card : ℤ) := by
    calc
      _ = ∑ _j ∈ support S 4, (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hn := ((mem_support S 4 j).mp hj).2
        rcases S.unit 4 j with h | h | h <;> simp_all
      _ = _ := by simp
  rw [hs, S.gram, S.principal_coefficient] at he
  simp [exceptionalCoefficients, exceptionalGram] at he
  exact_mod_cast he

public theorem support_triple (i : Fin 3) :
    ∃ a b c : J, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      support S (i.castLE (by decide)) = {a, b, c} := by
  classical
  exact Finset.card_eq_three.mp (support_card_three S i)

public theorem support_triple_at (i : Fin 3) (a : J)
    (ha : a ∈ support S (i.castLE (by decide))) :
    ∃ b c : J, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      support S (i.castLE (by decide)) = {a, b, c} := by
  classical
  have he : ((support S (i.castLE (by decide))).erase a).card = 2 := by
    rw [Finset.card_erase_of_mem ha, support_card_three]
  obtain ⟨b, c, hbc, he⟩ := Finset.card_eq_two.mp he
  have hb : b ∈ (support S (i.castLE (by decide))).erase a := by rw [he]; simp
  have hc : c ∈ (support S (i.castLE (by decide))).erase a := by rw [he]; simp
  refine ⟨b, c, (Finset.mem_erase.mp hb).1.symm, (Finset.mem_erase.mp hc).1.symm, hbc, ?_⟩
  conv_lhs => rw [← Finset.insert_erase ha, he]

public theorem signed_weight (i : Fin 5) (j : J) (hj : S.coefficient i j ≠ 0) :
    weight (signed i (S.degree j, fun l => S.coefficient l j)) =
      (S.coefficient i j : ℚ) * (columnValue (fun l => S.coefficient l j) 0 : ℚ)^2 /
        S.degree j := by
  have hv : columnValue (signed i (S.degree j, fun l => S.coefficient l j)).2 0 =
      S.coefficient i j * columnValue (fun l => S.coefficient l j) 0 := by
    dsimp [columnValue, signed]
    ring
  dsimp [weight]
  rw [hv]
  dsimp [signed]
  push_cast
  rcases S.unit i j with h | h | h
  · exact (hj h).elim
  · simp [h]
  · simp [h, div_neg, neg_div]

public theorem support_equations (i : Fin 3) {a b c : J}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hs : support S (i.castLE (by decide)) = {a, b, c}) :
    Triple (i.castLE (by decide))
      (signed (i.castLE (by decide)) (S.degree a, fun l => S.coefficient l a))
      (signed (i.castLE (by decide)) (S.degree b, fun l => S.coefficient l b))
      (signed (i.castLE (by decide)) (S.degree c, fun l => S.coefficient l c)) := by
  classical
  let k : Fin 5 := i.castLE (by decide)
  have sum_three {A : Type} [AddCommMonoid A] (f : J → A) :
      (∑ j ∈ support S k, f j) = f a + f b + f c := by
    rw [hs]
    simp [hab, hac, hbc, add_assoc]
  refine ⟨?_, ?_, ?_⟩
  · have h := sum_support S k (fun j => S.coefficient k j * (S.degree j : ℤ))
      (by intro j hj; simp [hj])
    rw [sum_three, S.principal_degree, S.principal_coefficient, S.degree_zero] at h
    dsimp [signed, targetDegree]
    dsimp [k] at h
    omega
  · intro l
    have h := sum_support S k (fun j => S.coefficient k j * S.coefficient l j)
      (by intro j hj; simp [hj])
    rw [sum_three, S.principal_coefficient, S.principal_coefficient, S.gram] at h
    dsimp [signed, targetGram]
    dsimp [k] at h
    omega
  · let f (j : J) : ℚ := (S.coefficient k j : ℚ) *
      (columnValue (fun l => S.coefficient l j) 0 : ℚ)^2 / S.degree j
    have he := sum_support S k f (by intro j hj; simp [f, hj])
    have hp : f S.principal = (exceptionalCoefficients k 0 : ℚ) := by
      simp [f, S.principal_degree, S.principal_coefficient, columnValue, exceptionalCoefficients]
    have hw (j : J) (hj : j ∈ support S k) :
        weight (signed k (S.degree j, fun l => S.coefficient l j)) = f j :=
      signed_weight S k j ((mem_support S k j).mp hj).2
    have ha : a ∈ support S k := by rw [hs]; simp
    have hb : b ∈ support S k := by rw [hs]; simp
    have hc : c ∈ support S k := by rw [hs]; simp
    change weight (signed k _) + weight (signed k _) + weight (signed k _) = targetSuzuki k
    rw [hw a ha, hw b hb, hw c hc]
    rw [sum_three, hp] at he
    have hu := S.suzuki k
    change (443520 : ℚ) / 147456 * ∑ j, f j = pairingConstants k at hu
    rw [← he] at hu
    norm_num at hu
    dsimp [targetSuzuki]
    linarith

end
end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21.SmallDegrees.Arithmetic
