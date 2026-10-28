module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.SmallModels
public import Theory.GroupTheory.CentralizerResidualProducts
public import Theory.GroupAction.InnerInvolutionGeometry

/-!
# Distinguishing A₇ from the smaller A.3.12 models

Exact orders exclude the binary, small alternating and small linear models.
A₇ contains a cubic, excluding Suzuki, while the odd PSL₂ order formula
would force the impossible field order eighteen. Simplicity and perfectness
also give the trivial center and solvable normal-subgroup obstruction.
Source: Aschbacher–Smith A.3.12 and C.5.12, pp.47–48,163.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection.AlternatingSevenMaximal
open Chapter1.Section02.LocalModels
variable {B : Type*} [Group B]

theorem card_of_model (h : IsAlternating B 7) : Nat.card B = 2520 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
  norm_num

theorem simple_of_model (h : IsAlternating B 7) : IsSimpleGroup B := by
  obtain ⟨e⟩ := h
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  exact e.isSimpleGroup

theorem perfect_of_model (h : IsAlternating B 7) : Group.IsPerfect B := by
  obtain ⟨e⟩ := h
  let : Group.IsPerfect (alternatingGroup (Fin 7)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem center_of_model (h : IsAlternating B 7) : center B = ⊥ := by
  let : IsSimpleGroup B := simple_of_model h
  let : Group.IsPerfect B := perfect_of_model h
  exact center_eq_bot_of_simple_perfect

theorem solvable_normal_eq_bot (h : IsAlternating B 7) (N : Subgroup B)
    [N.Normal] (hs : Group.IsSolvable N) : N = ⊥ := by
  let : IsSimpleGroup B := simple_of_model h
  let : Group.IsPerfect B := perfect_of_model h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N inferInstance with he | he
  · exact he
  · let : Group.IsSolvable N := hs
    let e := (MulEquiv.subgroupCongr he).trans topEquiv
    let : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective
      (f := e.symm.toMonoidHom) e.symm.injective
    exact (Group.IsPerfect.not_isSolvable B inferInstance).elim

theorem primeCore_eq_bot [Finite B] (h : IsAlternating B 7)
    (p : ℕ) [Fact p.Prime] : pCore p B = ⊥ := by
  let : Group.IsNilpotent (pCore p B) := pCore_isPGroup.isNilpotent
  exact solvable_normal_eq_bot h _ inferInstance

theorem not_binary (h : IsAlternating B 7) {n : ℕ} (hn : 0<n) :
    ¬ ClassicalGroup.IsPSL B 2 (2^n) := by
  intro hb
  have hv := binary_two_valuation hn hb
  have he : Nat.factorization 2520 2 = 3 := by
    rw [show 2520 = 2^3*315 by decide,Nat.factorization_mul (by decide) (by decide),
      Finsupp.add_apply,Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬2∣315)]
  rw [card_of_model h,he] at hv
  have hc := binary_card hb
  rw [← hv,card_of_model h] at hc
  norm_num at hc

theorem not_alternating_five (h : IsAlternating B 7) : ¬ IsAlternating B 5 := by
  rintro ⟨e⟩
  have hc := card_of_model h
  rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup] at hc
  norm_num at hc

theorem not_alternating_six (h : IsAlternating B 7) : ¬ IsAlternating B 6 := by
  rintro ⟨e⟩
  have hc := card_of_model h
  rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup] at hc
  norm_num at hc

theorem not_alternating_cover_six (h : IsAlternating B 7) : ¬ IsAlternatingCover B 6 := by
  rintro ⟨_,⟨ez⟩,⟨eq⟩⟩
  have hc := card_of_model h
  rw [card_eq_card_quotient_mul_card_subgroup (center B),
    Nat.card_congr eq.toEquiv,Nat.card_congr ez.toEquiv,nat_card_alternatingGroup] at hc
  norm_num at hc

theorem not_linear_three_two (h : IsAlternating B 7) : ¬ ClassicalGroup.IsPSL B 3 2 := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  rw [← Nat.card_congr e.toEquiv,card_of_model h,hF] at hc
  norm_num [Fin.prod_univ_succ] at hc

theorem not_linear_four_two (h : IsAlternating B 7) : ¬ ClassicalGroup.IsPSL B 4 2 := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
  rw [← Nat.card_congr e.toEquiv,card_of_model h,hF] at hc
  norm_num [Fin.prod_univ_succ] at hc

theorem not_linear_three_four (h : IsAlternating B 7) : ¬ ClassicalGroup.IsPSL B 3 4 := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  rw [← Nat.card_congr e.toEquiv,card_of_model h,hF] at hc
  norm_num [Fin.prod_univ_succ] at hc

theorem not_mathieu_twenty_two (h : IsAlternating B 7) : ¬ Nonempty (B ≃* Sporadic.Mathieu.M22) := by
  rintro ⟨e⟩
  have hc := card_of_model h
  rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m22_order] at hc
  norm_num at hc

theorem not_suzuki (h : IsAlternating B 7) (m : ℕ) (hm : 0<m) :
    ¬ Nonempty (B ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  rintro ⟨e⟩
  have hdiv : 3 ∣ Nat.card B := by rw [card_of_model h]; decide
  rw [Nat.card_congr e.toEquiv,BenderSuzuki.lemma115_suzukiMatrixGroup_card_formula m hm] at hdiv
  have hmod : 2^(2*m+1)%3 = 2 := by simp [pow_add,pow_mul,Nat.mul_mod,Nat.pow_mod]
  generalize hq : 2^(2*m+1) = q at hdiv hmod
  have hsub : (q-1)%3 = 1 := by omega
  have he := Nat.mod_eq_zero_of_dvd hdiv
  have hsquare : (q^2 + 1)%3 = 2 := by rw [Nat.add_mod,Nat.pow_mod,hmod]
  norm_num [Nat.mul_mod,Nat.pow_mod,hmod,hsub,hsquare] at he

theorem not_odd_linear_two (h : IsAlternating B 7) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) : ¬ ClassicalGroup.IsPSL B 2 p := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p,1,hp,ho,by decide,by simpa using hF⟩
  have hc : p*(p^2-1)/2 = 2520 := by
    rw [← hF,← GorensteinWalter.psl2_card_formula F hodd,← Nat.card_congr e.toEquiv]
    exact card_of_model h
  have hp18 : p = 18 := by
    have h1 : 18 ≤ p := by
      by_contra hh
      have hle : p ≤ 17 := by omega
      have hsq : p^2-1 ≤ 288 := by have := Nat.pow_le_pow_left hle 2; omega
      have := Nat.mul_le_mul hle hsq
      omega
    have h2 : p ≤ 18 := by
      by_contra hh
      have hle : 19 ≤ p := by omega
      have hsq : 360 ≤ p^2-1 := by have := Nat.pow_le_pow_left hle 2; omega
      have := Nat.mul_le_mul hle hsq
      omega
    omega
  rw [hp18] at ho
  norm_num at ho
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection.AlternatingSevenMaximal
