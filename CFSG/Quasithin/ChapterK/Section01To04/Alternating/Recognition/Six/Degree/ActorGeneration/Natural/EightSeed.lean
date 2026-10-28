module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.Degree.ActorGeneration.Contracts
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.ElementaryPair
import Mathlib.Tactic.FinCases

/-!
# Two conjugates of a natural elementary eight-group

Start with the three disjoint transpositions on six letters. Conjugating by
the even five-cycle (12345) supplies another matching. Four words of length
at most four give the star three-cycles based at 0 and 1. Their structural
generation theorem proves containment of A₆. Only small permutation identities
and the eight-element embedding are checked by kernel reduction.

Source: the group-generation bound used for Aschbacher–Smith K.1.1, printed
p.452 / PDF p.463, citing GM02 Theorem 6.2 and Table 6.3. This is an intrinsic
generation calculation, not the full representation-theoretic conclusion.
-/

public section

open Equiv Subgroup AlternatingSix.ShadowLocal
namespace CFSG.Quasithin.ChapterK.Alternating.SixDegreeReduction.ActorGenerationProof.NaturalProof
local notation "S6" => Perm (Fin 6)
local notation "Eight" => Holomorph.ElementaryPair.Eight

private def seedHom : Eight →* S6 where
  toFun i := (if i.1 = 1 then 1 else swap 0 1) *
    (if i.2.1 = 1 then 1 else swap 2 3) * (if i.2.2 = 1 then 1 else swap 4 5)
  map_one' := rfl
  map_mul' := by decide +kernel

def seedPerm : Subgroup S6 := seedHom.range

private theorem seedHom_injective : Function.Injective seedHom := by decide +kernel

instance seedPerm_elementary : IsElementaryAbelian 2 seedPerm :=
  IsElementaryAbelian.of_surjective seedHom.rangeRestrict seedHom.rangeRestrict_surjective

theorem card_seedPerm : Nat.card seedPerm = 8 := by
  rw [seedPerm, ← Nat.card_congr (MonoidHom.ofInjective seedHom_injective).toEquiv]
  simp [Holomorph.ElementaryPair.Eight, Holomorph.E4, Holomorph.C2]

private def q : A6 := ⟨swap 1 2 * swap 2 3 * swap 3 4 * swap 4 5,
  by rw [Perm.mem_alternatingGroup]; decide +kernel⟩

private def generators : Fin 6 → S6 :=
  ![swap 0 1, swap 2 3, swap 4 5, swap 0 2, swap 3 4, swap 1 5]

private def word : List (Fin 6) → S6
  | [] => 1
  | i :: w => generators i * word w

private theorem word_mem (H : Subgroup S6) (h : ∀ i, generators i ∈ H)
    (w : List (Fin 6)) : word w ∈ H := by
  induction w with
  | nil => exact H.one_mem
  | cons i w ih => exact H.mul_mem (h i) ih

private theorem seed_sup_generation : alternatingGroup (Fin 6) ≤
    seedPerm ⊔ seedPerm.map (MulAut.conj (q : S6)).toMonoidHom := by
  let H := seedPerm ⊔ seedPerm.map (MulAut.conj (q : S6)).toMonoidHom
  have ha : swap (0 : Fin 6) 1 ∈ seedPerm := ⟨(.ofAdd 1,1,1), by decide +kernel⟩
  have hb : swap (2 : Fin 6) 3 ∈ seedPerm := ⟨(1,.ofAdd 1,1), by decide +kernel⟩
  have hc : swap (4 : Fin 6) 5 ∈ seedPerm := ⟨(1,1,.ofAdd 1), by decide +kernel⟩
  have hmem (i : Fin 6) : generators i ∈ H := by
    fin_cases i
    · exact (show seedPerm ≤ H from le_sup_left) ha
    · exact (show seedPerm ≤ H from le_sup_left) hb
    · exact (show seedPerm ≤ H from le_sup_left) hc
    · apply (show seedPerm.map (MulAut.conj (q : S6)).toMonoidHom ≤ H from le_sup_right)
      convert mem_map_of_mem (MulAut.conj (q : S6)).toMonoidHom ha using 1
      decide +kernel
    · apply (show seedPerm.map (MulAut.conj (q : S6)).toMonoidHom ≤ H from le_sup_right)
      convert mem_map_of_mem (MulAut.conj (q : S6)).toMonoidHom hb using 1
      decide +kernel
    · apply (show seedPerm.map (MulAut.conj (q : S6)).toMonoidHom ≤ H from le_sup_right)
      convert mem_map_of_mem (MulAut.conj (q : S6)).toMonoidHom hc using 1
      decide +kernel
  have htop : (⊤ : Subgroup A6) ≤ H.comap (alternatingGroup (Fin 6)).subtype := by
    rw [← GLS3.Chapter5.starThreeCycles_closure_eq_top (a := (0 : Fin 6)) (b := 1) (by decide)]
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨i,hi0,hi1,he⟩
    change (x : S6) ∈ H
    rw [he]
    fin_cases i
    · exact (hi0 rfl).elim
    · exact (hi1 rfl).elim
    · convert word_mem H hmem [0,3] using 1
      decide +kernel
    · convert word_mem H hmem [1,0,3,1] using 1
      decide +kernel
    · convert word_mem H hmem [2,5,2,0] using 1
      decide +kernel
    · convert word_mem H hmem [5,0] using 1
      decide +kernel
  exact fun x hx => htop (show (⟨x,hx⟩ : A6) ∈ (⊤ : Subgroup A6) from mem_top _)

theorem seed_two_conjugates : ∃ c : Fin 2 → A6, alternatingGroup (Fin 6) ≤
    ⨆ i, seedPerm.map (MulAut.conj (c i : S6)).toMonoidHom := by
  let c : Fin 2 → A6 := ![1,q]
  refine ⟨c, seed_sup_generation.trans (sup_le ?_ ?_)⟩
  · have h0 := le_iSup (fun i : Fin 2 =>
      seedPerm.map (MulAut.conj (c i : S6)).toMonoidHom) (0 : Fin 2)
    change seedPerm.map (MulAut.conj (1 : S6)).toMonoidHom ≤ _ at h0
    rw [map_one] at h0
    change seedPerm.map (MonoidHom.id S6) ≤ _ at h0
    rw [Subgroup.map_id] at h0
    exact h0
  · exact le_iSup (fun i : Fin 2 =>
      seedPerm.map (MulAut.conj (c i : S6)).toMonoidHom) (1 : Fin 2)
end CFSG.Quasithin.ChapterK.Alternating.SixDegreeReduction.ActorGenerationProof.NaturalProof
