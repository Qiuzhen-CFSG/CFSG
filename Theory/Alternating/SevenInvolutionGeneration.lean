module

public import Theory.Alternating.theorem_5_2_1_2
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Three conjugate involutions generate A₇

Every nonidentity involution of the actual alternating group on seven points
has cycle type `(2,2)`. Mathlib's conjugacy theorem corrects the parity of a
symmetric-group conjugator using two fixed points, giving conjugacy inside A₇.

For `a = (01)(23)`, take `b = (14)(26)` and `c = (16)(25)`. The elements `ab`
and `ac` conjugate `a` to `b` and `c`. Five short words in `a,b,c` give the
inverses of all star three-cycles based at `0,1`, so the existing structural
star-generation theorem proves that these three involutions generate A₇.
Only the explicit word identities are checked by finite kernel reduction.
Conjugation transports this generating triple to every involution.

This is the intrinsic generation fact used in the alternating-cover exclusion
for Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, B.1.13 (printed pp.73–74/PDF pp.84–85), with the
alternating-group applications in K.1 (printed p.452/PDF p.463). It does not
assert those full representation-theoretic results. The cycle-type argument
adapts the project's proofs in `GorensteinWalter/ASevenInvariantOddPSubgroupCentralized.lean`
and the Held A₇ root-factor `SymmetricExtension.lean`, keeping imports in Theory.
-/

open Equiv Subgroup
namespace alternatingGroup.SevenInvolutionGeneration
private abbrev A7 := alternatingGroup (Fin 7)
private def a : A7 := ⟨swap 0 1 * swap 2 3, by rw [Perm.mem_alternatingGroup]; decide +kernel⟩
private def b : A7 := ⟨swap 1 4 * swap 2 6, by rw [Perm.mem_alternatingGroup]; decide +kernel⟩
private def c : A7 := ⟨swap 1 6 * swap 2 5, by rw [Perm.mem_alternatingGroup]; decide +kernel⟩

private theorem involution_cycleType (x : A7) (hx : x ≠ 1) (hx2 : x ^ 2 = 1) :
    (x : Perm (Fin 7)).cycleType = {2, 2} := by
  have ho : orderOf (x : Perm (Fin 7)) = 2 :=
    (Subgroup.orderOf_coe x).trans (orderOf_eq_prime hx2 hx)
  obtain ⟨k, hk⟩ := Perm.cycleType_prime_order (ho ▸ Nat.prime_two)
  rw [ho] at hk
  have hbound := (x : Perm (Fin 7)).sum_cycleType_le
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

private theorem involution_isConj (x : A7) (hx : x ≠ 1) (hx2 : x ^ 2 = 1) :
    IsConj a x := by
  have ha : (a : Perm (Fin 7)).cycleType = {2, 2} := by decide +kernel
  apply alternatingGroup.isConj_of
    (Perm.isConj_iff_cycleType_eq.mpr (ha.trans (involution_cycleType x hx hx2).symm))
  rw [← Perm.sum_cycleType, ha]
  decide

private def word : List (Fin 3) → A7
  | [] => 1
  | i :: w => (if i = 0 then a else if i = 1 then b else c) * word w

private theorem word_mem (H : Subgroup A7) (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H)
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
  let H : Subgroup A7 := zpowers a ⊔ zpowers b ⊔ zpowers c
  have ha : a ∈ H := (show zpowers a ≤ H from le_sup_left.trans le_sup_left) (mem_zpowers a)
  have hb : b ∈ H := (show zpowers b ≤ H from le_sup_right.trans le_sup_left) (mem_zpowers b)
  have hc : c ∈ H := (show zpowers c ≤ H from le_sup_right) (mem_zpowers c)
  have hstar (i : Fin 7) (hi0 : i ≠ 0) (hi1 : i ≠ 1) :
      (⟨swap 0 1 * swap 0 i,
        (Perm.isThreeCycle_swap_mul_swap_same (by decide) hi0.symm hi1.symm).mem_alternatingGroup⟩ : A7) ∈ H := by
    fin_cases i
    · exact (hi0 rfl).elim
    · exact (hi1 rfl).elim
    · convert H.inv_mem (word_mem H ha hb hc [1, 2, 0, 1, 0, 2, 1, 2, 0, 1, 2, 1, 0, 2]) using 1
      apply Subtype.ext
      change swap (0 : Fin 7) 1 * swap 0 2 = (word [1, 2, 0, 1, 0, 2, 1, 2, 0, 1, 2, 1, 0, 2] : Perm (Fin 7))⁻¹
      decide +kernel
    · convert H.inv_mem (word_mem H ha hb hc [0, 1, 0, 2, 1, 2, 0, 1, 2, 1, 0, 2, 0, 1, 2]) using 1
      apply Subtype.ext
      change swap (0 : Fin 7) 1 * swap 0 3 = (word [0, 1, 0, 2, 1, 2, 0, 1, 2, 1, 0, 2, 0, 1, 2] : Perm (Fin 7))⁻¹
      decide +kernel
    · convert H.inv_mem (word_mem H ha hb hc [0, 1, 2, 1, 2, 0, 1, 2, 1, 0, 2, 1, 2, 1]) using 1
      apply Subtype.ext
      change swap (0 : Fin 7) 1 * swap 0 4 = (word [0, 1, 2, 1, 2, 0, 1, 2, 1, 0, 2, 1, 2, 1] : Perm (Fin 7))⁻¹
      decide +kernel
    · convert H.inv_mem (word_mem H ha hb hc [2, 1, 0, 2, 0, 1, 2, 0]) using 1
      apply Subtype.ext
      change swap (0 : Fin 7) 1 * swap 0 5 = (word [2, 1, 0, 2, 0, 1, 2, 0] : Perm (Fin 7))⁻¹
      decide +kernel
    · convert H.inv_mem (word_mem H ha hb hc [2, 1, 2, 1, 0, 2, 1, 2, 0, 1, 2, 1]) using 1
      apply Subtype.ext
      change swap (0 : Fin 7) 1 * swap 0 6 = (word [2, 1, 2, 1, 0, 2, 1, 2, 0, 1, 2, 1] : Perm (Fin 7))⁻¹
      decide +kernel
  apply top_unique
  rw [← GLS3.Chapter5.starThreeCycles_closure_eq_top (a := (0 : Fin 7)) (b := 1) (by decide)]
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨i, hi0, hi1, hi⟩
  have heq : x = (⟨swap 0 1 * swap 0 i,
      (Perm.isThreeCycle_swap_mul_swap_same (by decide) hi0.symm hi1.symm).mem_alternatingGroup⟩ : A7) :=
    Subtype.ext hi
  rw [heq]
  exact hstar i hi0 hi1

private theorem seed_three_conjugates :
    ∃ g h : A7, zpowers a ⊔ zpowers (g * a * g⁻¹) ⊔ zpowers (h * a * h⁻¹) = ⊤ := by
  refine ⟨a * b, a * c, ?_⟩
  have hb : (a * b) * a * (a * b)⁻¹ = b := by decide +kernel
  have hc : (a * c) * a * (a * c)⁻¹ = c := by decide +kernel
  rw [hb, hc]
  exact seed_generates

/-- Every nonidentity involution of A₇ generates A₇ together with two
conjugates by elements of A₇ itself. -/
public theorem three_conjugates_generate (x : alternatingGroup (Fin 7)) (hx : x ≠ 1)
    (hx2 : x ^ 2 = 1) :
    ∃ g h : alternatingGroup (Fin 7),
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

end alternatingGroup.SevenInvolutionGeneration
