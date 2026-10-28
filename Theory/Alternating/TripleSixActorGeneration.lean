module

public import Theory.Alternating.theorem_5_2_1_2
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Three conjugate involutions generate A₆

Every involution is a double transposition, with two fixed points allowing
its symmetric conjugator to be chosen even. The three double transpositions
(01)(23), (01)(24), and (02)(15) generate all star three-cycles. Short word
identities are checked by kernel reduction, then conjugacy gives the result
for every nonidentity involution.

This is the inner generation input for the triple-A₆ degree bound in
Aschbacher–Smith K.1 (printed pp.452–453). The proof adapts the structural
pattern in `Theory.Alternating.SevenInvolutionGeneration`, with separate
six-letter generators and checked identities.
-/

open Equiv Subgroup
namespace alternatingGroup.TripleSixActorGeneration
private abbrev A6 := alternatingGroup (Fin 6)
private def a : A6 := ⟨swap 0 1 * swap 2 3, by rw [Perm.mem_alternatingGroup]; decide +kernel⟩
private def b : A6 := ⟨swap 0 1 * swap 2 4, by rw [Perm.mem_alternatingGroup]; decide +kernel⟩
private def c : A6 := ⟨swap 0 2 * swap 1 5, by rw [Perm.mem_alternatingGroup]; decide +kernel⟩

private theorem involution_cycleType (x : A6) (hx : x ≠ 1) (hx2 : x ^ 2 = 1) :
    (x : Perm (Fin 6)).cycleType = {2, 2} := by
  have ho : orderOf (x : Perm (Fin 6)) = 2 :=
    (Subgroup.orderOf_coe x).trans (orderOf_eq_prime hx2 hx)
  obtain ⟨k, hk⟩ := Perm.cycleType_prime_order (ho ▸ Nat.prime_two)
  rw [ho] at hk
  have hbound := (x : Perm (Fin 6)).sum_cycleType_le
  rw [hk] at hbound
  simp only [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, Fintype.card_fin] at hbound
  have hsign := Perm.mem_alternatingGroup.mp x.property
  rw [Perm.sign_of_cycleType', hk] at hsign
  have hkbound : k ≤ 2 := by omega
  have hk1 : k = 1 := by
    interval_cases k
    · norm_num at hsign
    · rfl
    · norm_num at hsign
  simpa [hk1] using hk

private theorem involution_isConj (x : A6) (hx : x ≠ 1) (hx2 : x ^ 2 = 1) :
    IsConj a x := by
  have ha : (a : Perm (Fin 6)).cycleType = {2, 2} := by decide +kernel
  apply alternatingGroup.isConj_of
    (Perm.isConj_iff_cycleType_eq.mpr (ha.trans (involution_cycleType x hx hx2).symm))
  rw [← Perm.sum_cycleType, ha]
  decide

private def word : List (Fin 3) → A6
  | [] => 1
  | i :: w => (if i = 0 then a else if i = 1 then b else c) * word w

private theorem word_mem (H : Subgroup A6) (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H)
    (w : List (Fin 3)) : word w ∈ H := by
  induction w with
  | nil => exact H.one_mem
  | cons i w ih =>
    apply H.mul_mem ?_ ih
    fin_cases i
    · exact ha
    · exact hb
    · exact hc

private theorem seed_generates : zpowers a ⊔ zpowers b ⊔ zpowers c = ⊤ := by
  let H : Subgroup A6 := zpowers a ⊔ zpowers b ⊔ zpowers c
  have ha : a ∈ H := (show zpowers a ≤ H from le_sup_left.trans le_sup_left) (mem_zpowers a)
  have hb : b ∈ H := (show zpowers b ≤ H from le_sup_right.trans le_sup_left) (mem_zpowers b)
  have hc : c ∈ H := (show zpowers c ≤ H from le_sup_right) (mem_zpowers c)
  have hstar (i : Fin 6) (hi0 : i ≠ 0) (hi1 : i ≠ 1) :
      (⟨swap 0 1 * swap 0 i,
        (Perm.isThreeCycle_swap_mul_swap_same (by decide) hi0.symm hi1.symm).mem_alternatingGroup⟩ : A6) ∈ H := by
    fin_cases i
    · exact (hi0 rfl).elim
    · exact (hi1 rfl).elim
    · convert word_mem H ha hb hc [1, 2, 0, 1, 2, 1, 0] using 1
      apply Subtype.ext
      change swap (0 : Fin 6) 1 * swap 0 2 = (word [1, 2, 0, 1, 2, 1, 0] : Perm (Fin 6))
      decide +kernel
    · convert word_mem H ha hb hc [1, 2, 1, 0, 2, 1, 0] using 1
      apply Subtype.ext
      change swap (0 : Fin 6) 1 * swap 0 3 = (word [1, 2, 1, 0, 2, 1, 0] : Perm (Fin 6))
      decide +kernel
    · convert word_mem H ha hb hc [0, 2, 0, 1, 2, 0, 1] using 1
      apply Subtype.ext
      change swap (0 : Fin 6) 1 * swap 0 4 = (word [0, 2, 0, 1, 2, 0, 1] : Perm (Fin 6))
      decide +kernel
    · convert word_mem H ha hb hc [2, 1, 0, 2, 0, 1, 2, 0] using 1
      apply Subtype.ext
      change swap (0 : Fin 6) 1 * swap 0 5 = (word [2, 1, 0, 2, 0, 1, 2, 0] : Perm (Fin 6))
      decide +kernel
  apply top_unique
  rw [← GLS3.Chapter5.starThreeCycles_closure_eq_top (a := (0 : Fin 6)) (b := 1) (by decide)]
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨i, hi0, hi1, hi⟩
  have heq : x = (⟨swap 0 1 * swap 0 i,
      (Perm.isThreeCycle_swap_mul_swap_same (by decide) hi0.symm hi1.symm).mem_alternatingGroup⟩ : A6) :=
    Subtype.ext hi
  rw [heq]
  exact hstar i hi0 hi1

private theorem seed_three_conjugates :
    ∃ g h : A6, zpowers a ⊔ zpowers (g * a * g⁻¹) ⊔ zpowers (h * a * h⁻¹) = ⊤ := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (involution_isConj b (by decide +kernel) (by decide +kernel))
  obtain ⟨h, hh⟩ := isConj_iff.mp (involution_isConj c (by decide +kernel) (by decide +kernel))
  exact ⟨g, h, by rw [hg, hh]; exact seed_generates⟩

/-- Every nonidentity involution of A₆ generates A₆ together with two
conjugates by elements of A₆ itself. -/
public theorem three_conjugates_generate (x : alternatingGroup (Fin 6)) (hx : x ≠ 1)
    (hx2 : x ^ 2 = 1) :
    ∃ g h : alternatingGroup (Fin 6),
      zpowers x ⊔ zpowers (g * x * g⁻¹) ⊔ zpowers (h * x * h⁻¹) = ⊤ := by
  obtain ⟨q, hq⟩ := isConj_iff.mp (involution_isConj x hx hx2)
  let e := MulAut.conj q
  have he : e a = x := hq
  obtain ⟨g, h, hgh⟩ := seed_three_conjugates
  refine ⟨e g, e h, ?_⟩
  have hm := congrArg (Subgroup.map e.toMonoidHom) hgh
  rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers,
    MonoidHom.map_zpowers, MonoidHom.map_zpowers,
    Subgroup.map_top_of_surjective _ e.surjective] at hm
  simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, map_mul, map_inv, he] using hm

end alternatingGroup.TripleSixActorGeneration
