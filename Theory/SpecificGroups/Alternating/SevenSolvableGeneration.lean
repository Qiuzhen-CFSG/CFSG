module

public import Theory.Alternating.theorem_5_2_1_2
public import Theory.GroupTheory.TwoThreeSolvable

/-!
# Solvable local subgroups generating the alternating group on seven letters

In S₇ the centralizers of (01)(23) and (01)(23)(45) have order 48 and
contain the same Sylow two-subgroup of order 16. Their intersections with A₇
generate A₇: a three-cycle on {4,5,6}, and its conjugates under the paired
three-cycle (024)(135), give three three-cycles with common letter 6.
Short words in these yield the usual star generators of A₇.

The finite certificates concern only sixteen permutations and pointwise word
identities. Centralizer orders use the cycle-type formula; solvability follows
from the proved two-prime theorem. Sylow conjugacy handles every two-subgroup.

This is the concrete solvable-overgroup argument for Aschbacher--Smith,
*The Classification of Quasithin Groups*, E.1.14(3), printed p.214,
which cites Aschbacher, *GF(2)-representations of finite groups*, Lemma 4.8.
The E-generation application is in ChapterE.Section01.ValuesOdd.AlternatingGeneration.
-/

@[expose] public section

open Subgroup Equiv Equiv.Perm
open scoped Pointwise
namespace alternatingGroup.SevenSolvableGeneration

local notation "S" => Perm (Fin 7)
private def u : S := swap 0 1 * swap 2 3
private def v : S := u * swap 4 5

def leftLocal : Subgroup S := centralizer {swap 0 1 * swap 2 3}
def rightLocal : Subgroup S := centralizer {swap 0 1 * swap 2 3 * swap 4 5}

private def r : S := swap 0 2 * swap 0 1 * swap 0 3
private def s : S := swap 0 1
private def z : S := swap 4 5
private def word (i : Fin 4) (j k : Fin 2) : S := r ^ i.val * s ^ j.val * z ^ k.val

private theorem word_mul : ∀ (i : Fin 4) (j k : Fin 2) (l : Fin 4) (m n : Fin 2),
    word i j k * word l m n =
      word ⟨(i.val + if j = 0 then l.val else 4 - l.val) % 4, Nat.mod_lt _ (by decide)⟩
        ⟨(j.val + m.val) % 2, Nat.mod_lt _ (by decide)⟩
        ⟨(k.val + n.val) % 2, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

private theorem word_inv : ∀ (i : Fin 4) (j k : Fin 2),
    (word i j k)⁻¹ =
      word ⟨(if j = 0 then 4 - i.val else i.val) % 4, Nat.mod_lt _ (by decide)⟩ j k := by
  decide +kernel

private def standardTwo : Subgroup S where
  carrier := {g | ∃ i j k, word i j k = g}
  one_mem' := ⟨0, 0, 0, by decide⟩
  mul_mem' := by
    rintro _ _ ⟨i, j, k, rfl⟩ ⟨l, m, n, rfl⟩
    exact ⟨_, _, _, (word_mul i j k l m n).symm⟩
  inv_mem' := by
    rintro _ ⟨i, j, k, rfl⟩
    exact ⟨_, _, _, (word_inv i j k).symm⟩

private def wordEmbedding : (Fin 4 × Fin 2 × Fin 2) → standardTwo :=
  fun x => ⟨word x.1 x.2.1 x.2.2, x.1, x.2.1, x.2.2, rfl⟩

private theorem word_injective : Function.Injective (fun x : Fin 4 × Fin 2 × Fin 2 =>
    word x.1 x.2.1 x.2.2) := by decide +kernel

private theorem standardTwo_card : Nat.card standardTwo = 16 := by
  have hi : Function.Injective wordEmbedding :=
    fun x y h => word_injective (congrArg Subtype.val h)
  have hs : Function.Surjective wordEmbedding := by
    rintro ⟨g, i, j, k, rfl⟩
    exact ⟨(i,j,k), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective wordEmbedding ⟨hi, hs⟩)]
  simp

private def standardSylow : Sylow 2 S := Sylow.ofCard standardTwo (by
  rw [standardTwo_card]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  decide +kernel)

private theorem standardTwo_le_left : standardTwo ≤ leftLocal := by
  rintro g ⟨i, j, k, rfl⟩
  exact mem_centralizer_singleton_iff.mpr (by
    revert i j k
    decide +kernel)

private theorem standardTwo_le_right : standardTwo ≤ rightLocal := by
  rintro g ⟨i, j, k, rfl⟩
  exact mem_centralizer_singleton_iff.mpr (by
    revert i j k
    decide +kernel)

private theorem leftLocal_card : Nat.card leftLocal = 48 := by
  have hu : u.cycleType = {2, 2} := by decide +kernel
  change Nat.card (centralizer ({u} : Set S)) = 48
  rw [nat_card_centralizer, hu]
  norm_num [Nat.factorial]

private theorem rightLocal_card : Nat.card rightLocal = 48 := by
  have hv : v.cycleType = {2, 2, 2} := by decide +kernel
  change Nat.card (centralizer ({v} : Set S)) = 48
  rw [nat_card_centralizer, hv]
  norm_num [Nat.factorial]

private theorem solvable_of_card_48 {H : Type*} [Group H] [Finite H]
    (hc : Nat.card H = 48) : Group.IsSolvable H := by
  apply Theory.GroupTheory.isSolvable_of_prime_dvd_card_eq_two_or_three H
  intro p hp hd
  rw [hc] at hd
  have hd' : p ∣ 2 ^ 4 * 3 := hd
  rcases hp.dvd_mul.mp hd' with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)

instance : Group.IsSolvable leftLocal := solvable_of_card_48 leftLocal_card
instance : Group.IsSolvable rightLocal := solvable_of_card_48 rightLocal_card

private def threeCycle (i j k : Fin 7) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    alternatingGroup (Fin 7) :=
  ⟨swap i j * swap i k,
    (isThreeCycle_swap_mul_swap_same hij hik hjk).mem_alternatingGroup⟩
private def a : alternatingGroup (Fin 7) := threeCycle 6 0 1 (by decide) (by decide) (by decide)
private def b : alternatingGroup (Fin 7) := threeCycle 6 2 3 (by decide) (by decide) (by decide)
private def c : alternatingGroup (Fin 7) := threeCycle 6 4 5 (by decide) (by decide) (by decide)
private def d : alternatingGroup (Fin 7) :=
  threeCycle 0 2 4 (by decide) (by decide) (by decide) *
    threeCycle 1 3 5 (by decide) (by decide) (by decide)

/-- The even parts of the two solvable local subgroups generate A₇. -/
theorem even_locals_generate :
    leftLocal.comap (alternatingGroup (Fin 7)).subtype ⊔
      rightLocal.comap (alternatingGroup (Fin 7)).subtype = ⊤ := by
  let H := leftLocal.comap (alternatingGroup (Fin 7)).subtype ⊔
      rightLocal.comap (alternatingGroup (Fin 7)).subtype
  have hc : c ∈ H := by
    apply (show leftLocal.comap (alternatingGroup (Fin 7)).subtype ≤ H from le_sup_left)
    exact mem_centralizer_singleton_iff.mpr (by ext x; fin_cases x <;> decide)
  have hd : d ∈ H := by
    apply (show rightLocal.comap (alternatingGroup (Fin 7)).subtype ≤ H from le_sup_right)
    exact mem_centralizer_singleton_iff.mpr (by ext x; fin_cases x <;> decide)
  have hb : b ∈ H := by
    have he : b = d * c * d⁻¹ := by apply Subtype.ext; ext x; fin_cases x <;> decide
    rw [he]
    exact H.mul_mem (H.mul_mem hd hc) (H.inv_mem hd)
  have ha : a ∈ H := by
    have he : a = d * b * d⁻¹ := by apply Subtype.ext; ext x; fin_cases x <;> decide
    rw [he]
    exact H.mul_mem (H.mul_mem hd hb) (H.inv_mem hd)
  apply top_unique
  rw [← GLS3.Chapter5.starThreeCycles_closure_eq_top (a := (0 : Fin 7)) (b := (1 : Fin 7)) (by decide), closure_le]
  rintro g ⟨x, hx0, hx1, hg⟩
  have identify (w : alternatingGroup (Fin 7))
      (hw : (w : S) = swap 0 1 * swap 0 x) : g = w := Subtype.ext (hg.trans hw.symm)
  fin_cases x
  · exact (hx0 rfl).elim
  · exact (hx1 rfl).elim
  · rw [identify (b * b * a * b) (by ext i; fin_cases i <;> decide)]
    exact H.mul_mem (H.mul_mem (H.mul_mem hb hb) ha) hb
  · rw [identify (b * a * b * b) (by ext i; fin_cases i <;> decide)]
    exact H.mul_mem (H.mul_mem (H.mul_mem hb ha) hb) hb
  · rw [identify (c * c * a * c) (by ext i; fin_cases i <;> decide)]
    exact H.mul_mem (H.mul_mem (H.mul_mem hc hc) ha) hc
  · rw [identify (c * a * c * c) (by ext i; fin_cases i <;> decide)]
    exact H.mul_mem (H.mul_mem (H.mul_mem hc ha) hc) hc
  · rw [identify a (by ext i; fin_cases i <;> decide)]
    exact ha

/-- Every two-subgroup can be conjugated into both solvable local subgroups. -/
theorem exists_conjugate_le_locals (U : Subgroup S) (hU : IsPGroup 2 U) :
    ∃ g : S, U.map (MulAut.conj g).toMonoidHom ≤ leftLocal ∧
      U.map (MulAut.conj g).toMonoidHom ≤ rightLocal := by
  obtain ⟨P, hP⟩ := hU.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S P standardSylow
  have he : (P : Subgroup S).map (MulAut.conj g).toMonoidHom = standardTwo := by
    change ((g • P : Sylow 2 S) : Subgroup S) = standardTwo
    rw [hg]
    rfl
  have hu : U.map (MulAut.conj g).toMonoidHom ≤ standardTwo := by
    rw [← he]
    exact map_mono hP
  exact ⟨g, hu.trans standardTwo_le_left, hu.trans standardTwo_le_right⟩

end alternatingGroup.SevenSolvableGeneration
