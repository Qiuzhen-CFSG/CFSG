module

public import Stellmacher.Recognition.LyonsU3Four.LocalFiveRestrictionSums
public import Theory.Character.ModularBlock.TwoElementColumnOrthogonality

/-!
# The principal two-block of the Lyons local group

Every ordinary irreducible of the supplied order-320 semidirect product lies
in its principal characteristic-two block. Reindex the constructed ordinary
table into the prescribed complete family. Principal-block column orthogonality
makes its degree-weighted character vanish on nonidentity Sylow elements.

Let D be the sum of squared degrees in the block, a the number of its
linear rows and b the number of its quintic rows. Summing on the Sylow
subgroup and on its center gives D = 64a and D = 4a + 100b. The principal
row gives 1 ≤ a ≤ 5, so these equations force a = 5 and D = 320.
The positive squared degrees then force every row into the block. This uses
only the genuine ordinary table and the proved block column orthogonality;
no modular table, class-size enumeration or block membership is assumed.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972),
Lemmas 2 and 4, pp. 373 and 381. The averaging argument is supplied here.
-/

public section

noncomputable section
open scoped BigOperators
open ModularBlock.PrincipalBlockConstruction
attribute [local instance] Fintype.ofFinite Classical.propDecidable
namespace Stellmacher.Recognition.LyonsU3Four
variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    {α : FiveComplement →* MulAut S}

/-- Identify the constructed ordinary table with the prescribed complete family. -/
def LocalFiveCharacterTable.blockIndex (T : LocalFiveCharacterTable S α)
    (d : PrincipalCongruenceBlockData (LocalFiveGroup S α)) : LocalFiveRowIndex S ≃ d.I := by
  let f (i : LocalFiveRowIndex S) := (d.complete.2.1 (T.row i) (T.row_complete.1 i)).choose
  have hf (i) : d.chi (f i) = T.row i :=
    (d.complete.2.1 (T.row i) (T.row_complete.1 i)).choose_spec
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro i j hij
    apply T.row_complete.2.2
    rw [← hf i, ← hf j, hij]
  · intro j
    obtain ⟨i, hi⟩ := T.row_complete.2.1 (d.chi j) (d.complete.1 j)
    exact ⟨i, d.complete.2.2 ((hf i).trans hi)⟩

/-- Reindexing preserves the actual ordinary character, not just its degree. -/
theorem LocalFiveCharacterTable.blockIndex_apply (T : LocalFiveCharacterTable S α)
    (d : PrincipalCongruenceBlockData (LocalFiveGroup S α)) (i : LocalFiveRowIndex S) :
    d.chi (T.blockIndex d i) = T.row i :=
  (d.complete.2.1 (T.row i) (T.row_complete.1 i)).choose_spec

private def weight (T : LocalFiveCharacterTable S α)
    (d : PrincipalCongruenceBlockData (LocalFiveGroup S α)) (i : LocalFiveRowIndex S) : ℕ :=
  if T.blockIndex d i ∈ d.block then 1 else 0

private theorem weighted_kernel (T : LocalFiveCharacterTable S α)
    (d : PrincipalCongruenceBlockData (LocalFiveGroup S α)) (s : S) :
    ∑ i : LocalFiveRowIndex S, (weight T d i : ℂ) * (localFiveRowDegree S i : ℂ) *
      star (T.row i (ConjClasses.mk (SemidirectProduct.inl s))) =
    ∑ j ∈ d.block, d.chi j (ConjClasses.mk 1) *
      star (d.chi j (ConjClasses.mk (SemidirectProduct.inl s))) := by
  have he := (T.blockIndex d).sum_comp (fun j => if j ∈ d.block then
    d.chi j (ConjClasses.mk 1) *
      star (d.chi j (ConjClasses.mk (SemidirectProduct.inl s))) else 0)
  simp only [T.blockIndex_apply, T.row_degree] at he
  simpa [weight, ite_mul, ← Finset.sum_filter] using he

private theorem weighted_kernel_zero (T : LocalFiveCharacterTable S α)
    (d : PrincipalCongruenceBlockData (LocalFiveGroup S α)) (s : S) (hs : s ≠ 1) :
    ∑ i : LocalFiveRowIndex S, (weight T d i : ℂ) * (localFiveRowDegree S i : ℂ) *
      star (T.row i (ConjClasses.mk (SemidirectProduct.inl s))) = 0 := by
  rw [weighted_kernel]
  apply ModularBlock.TwoElementColumnOrthogonality.principalBlock_column_orthogonal
  · exact ⟨0, by simp⟩
  · obtain ⟨n, hn⟩ := S.isPGroup'.exists_pow_pow_eq_one s
    exact ⟨n, by rw [← map_pow, hn, map_one]⟩
  · intro hc
    have he : (SemidirectProduct.inl s : LocalFiveGroup S α) = 1 := isConj_one_left.mp hc.symm
    exact hs (SemidirectProduct.inl_injective (he.trans (map_one _).symm))

private theorem weighted_kernel_value (T : LocalFiveCharacterTable S α)
    (d : PrincipalCongruenceBlockData (LocalFiveGroup S α)) (s : S) :
    ∑ i : LocalFiveRowIndex S, (weight T d i : ℂ) * (localFiveRowDegree S i : ℂ) *
      star (T.row i (ConjClasses.mk (SemidirectProduct.inl s))) =
    if s = 1 then (∑ i : LocalFiveRowIndex S, weight T d i * localFiveRowDegree S i ^ 2 : ℕ) else 0 := by
  by_cases hs : s = 1
  · subst s
    simp [T.row_degree, pow_two, mul_assoc]
  · rw [if_neg hs]
    simpa only [Nat.cast_zero] using weighted_kernel_zero T d s hs

private theorem weighted_sylow_sum (h : SylowStructure S) (T : LocalFiveCharacterTable S α)
    (d : PrincipalCongruenceBlockData (LocalFiveGroup S α)) :
    (∑ i : LocalFiveRowIndex S, weight T d i * localFiveRowDegree S i ^ 2) =
      64 * ∑ χ : FiveLinearIndex, weight T d (.inl χ) := by
  have he := congrArg (fun f : S → ℂ => ∑ s, f s) (funext (weighted_kernel_value T d))
  simp only [Nat.cast_ite, Nat.cast_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at he
  rw [Finset.sum_comm] at he
  simp only [← Finset.mul_sum, ← star_sum] at he
  have havg (i : LocalFiveRowIndex S) :
      (∑ s : S, T.row i (ConjClasses.mk (SemidirectProduct.inl s))) =
        (match i with | .inl _ => (64 : ℂ) | _ => 0) := by
    convert T.sum_sylow h i using 1
    cases i <;> rfl
  have he' :
      (∑ i : LocalFiveRowIndex S, (weight T d i : ℂ) * (localFiveRowDegree S i : ℂ) *
        star (match i with | .inl _ => (64 : ℂ) | _ => 0)) =
      ((∑ i : LocalFiveRowIndex S, weight T d i * localFiveRowDegree S i ^ 2 : ℕ) : ℂ) := by
    calc
      _ = ∑ i : LocalFiveRowIndex S, (weight T d i : ℂ) * (localFiveRowDegree S i : ℂ) *
          star (∑ s : S, T.row i (ConjClasses.mk (SemidirectProduct.inl s))) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [havg i]
      _ = _ := he
  conv_lhs at he' =>
    norm_num [Fintype.sum_sum_type, localFiveRowDegree, map_ofNat]
  have hh : ((64 * ∑ χ : FiveLinearIndex, weight T d (.inl χ) : ℕ) : ℂ) =
      ((∑ i : LocalFiveRowIndex S, weight T d i * localFiveRowDegree S i ^ 2 : ℕ) : ℂ) := by
    simpa only [Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat, Finset.mul_sum, mul_comm] using he'
  exact_mod_cast hh.symm

private theorem weighted_center_sum (h : SylowStructure S) (T : LocalFiveCharacterTable S α)
    (d : PrincipalCongruenceBlockData (LocalFiveGroup S α)) :
    (∑ i : LocalFiveRowIndex S, weight T d i * localFiveRowDegree S i ^ 2) =
      4 * (∑ χ : FiveLinearIndex, weight T d (.inl χ)) +
      100 * (∑ i : Fin 3, weight T d (.inr (.inr i))) := by
  have he := congrArg (fun f : Subgroup.center S → ℂ => ∑ s, f s)
    (funext (fun w => weighted_kernel_value T d (w : S)))
  have hone (w : Subgroup.center S) : (w : S) = 1 ↔ w = 1 :=
    ⟨fun hh => Subtype.ext hh, fun hh => congrArg Subtype.val hh⟩
  simp only [Nat.cast_ite, Nat.cast_zero, hone, Finset.sum_ite_eq', Finset.mem_univ, if_true] at he
  rw [Finset.sum_comm] at he
  simp_rw [← Finset.mul_sum, ← star_sum, T.sum_center h] at he
  conv_lhs at he =>
    norm_num [Fintype.sum_sum_type, localFiveRowDegree, map_ofNat]
  have hh : ((4 * (∑ χ : FiveLinearIndex, weight T d (.inl χ)) +
      100 * (∑ i : Fin 3, weight T d (.inr (.inr i))) : ℕ) : ℂ) =
      ((∑ i : LocalFiveRowIndex S, weight T d i * localFiveRowDegree S i ^ 2 : ℕ) : ℂ) := by
    convert he using 1
    push_cast
    simp only [← Finset.sum_mul]
    ring
  exact_mod_cast hh.symm


private theorem weight_le_one (T : LocalFiveCharacterTable S α)
    (d : PrincipalCongruenceBlockData (LocalFiveGroup S α)) (i : LocalFiveRowIndex S) :
    weight T d i ≤ 1 := by unfold weight; split_ifs <;> omega

private theorem linear_weight_pos (T : LocalFiveCharacterTable S α)
    (d : PrincipalCongruenceBlockData (LocalFiveGroup S α)) :
    0 < ∑ χ : FiveLinearIndex, weight T d (.inl χ) := by
  have hp : T.blockIndex d (.inl 1) = d.principal := by
    apply d.complete.2.2
    rw [T.blockIndex_apply, d.principal_eq]
    ext c
    obtain ⟨g, rfl⟩ := ConjClasses.exists_rep c
    simp [T.linear_value]
  have hw : weight T d (.inl 1) = 1 := by simp [weight, hp]
  have hs := Finset.single_le_sum (f := fun χ : FiveLinearIndex => weight T d (.inl χ))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ (1 : FiveLinearIndex))
  omega

private theorem total_degree_sum (h : SylowStructure S) :
    ∑ i : LocalFiveRowIndex S, localFiveRowDegree S i ^ 2 = 320 := by
  simp only [localFiveRowDegree, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
    fiveLinearIndex_card, quarticRowIndex_card S h]
  norm_num

/-- Sylow and center averages place every row of the actual table in the principal block. -/
theorem LocalFiveCharacterTable.block_eq_univ (h : SylowStructure S)
    (T : LocalFiveCharacterTable S α)
    (d : PrincipalCongruenceBlockData (LocalFiveGroup S α)) : d.block = Finset.univ := by
  have hs := weighted_sylow_sum h T d
  have hc := weighted_center_sum h T d
  have hl := linear_weight_pos T d
  have hb : (∑ χ : FiveLinearIndex, weight T d (.inl χ)) ≤ 5 := by
    calc
      _ ≤ ∑ _χ : FiveLinearIndex, 1 := Finset.sum_le_sum (fun χ _ => weight_le_one T d (.inl χ))
      _ = 5 := by simp [← Nat.card_eq_fintype_card, fiveLinearIndex_card]
  have hfive : (∑ χ : FiveLinearIndex, weight T d (.inl χ)) = 5 := by omega
  have hfull : (∑ i : LocalFiveRowIndex S, weight T d i * localFiveRowDegree S i ^ 2) =
      ∑ i : LocalFiveRowIndex S, localFiveRowDegree S i ^ 2 := by
    rw [hs, hfive, total_degree_sum h]
  have hpoint := (Finset.sum_eq_sum_iff_of_le (fun i (_ : i ∈ (Finset.univ : Finset (LocalFiveRowIndex S))) =>
    show weight T d i * localFiveRowDegree S i ^ 2 ≤ localFiveRowDegree S i ^ 2 from
      calc
        _ ≤ 1 * localFiveRowDegree S i ^ 2 := Nat.mul_le_mul_right _ (weight_le_one T d i)
        _ = _ := one_mul _)).mp hfull
  apply Finset.eq_univ_of_forall
  intro j
  obtain ⟨i, rfl⟩ := (T.blockIndex d).surjective j
  have hi := hpoint i (Finset.mem_univ i)
  by_contra hn
  have hw : weight T d i = 0 := by simp [weight, hn]
  rw [hw, zero_mul] at hi
  rcases i with χ | (p | i) <;> norm_num [localFiveRowDegree] at hi

/-- All ordinary irreducibles of the supplied Lyons local group belong to its
principal characteristic-two block, for every choice of congruence-block data. -/
theorem localFive_principalBlock_eq_univ (h : SylowStructure S) (β : MulAut S)
    (hβ : orderOf β = 15) (hα : α (Multiplicative.ofAdd 1) = β ^ (3 : ℕ))
    (d : PrincipalCongruenceBlockData (LocalFiveGroup S α)) : d.block = Finset.univ := by
  obtain ⟨T⟩ := exists_localFiveCharacterTable S α h β hβ hα
  exact T.block_eq_univ h d

end Stellmacher.Recognition.LyonsU3Four
