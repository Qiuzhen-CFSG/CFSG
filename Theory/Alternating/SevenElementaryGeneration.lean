module

public import Theory.Alternating.SevenInvolutionGeneration
public import Theory.Representation.AlternatingSevenConjugatePair.ElementaryGeometry
public import Theory.Representation.BinaryOffender.CentralCoverConjugateBudget
import Mathlib.Tactic.FinCases


/-!
# Elementary conjugate generation in A₇

Every nontrivial elementary two-subgroup of A₇ has rank one or two. The
rank-one case uses three conjugate involutions. For each of the two four-group
types, two conjugates generate A₇: ten short word identities give all the star
three-cycles, and the structural star-generation theorem finishes the proof.
The identities are checked by kernel reduction on seven points.

The elementary geometry places an arbitrary four-group into a standard model
by a symmetric permutation. Conjugation by that permutation restricts to an
automorphism of A₇. Transporting the standard generating pair through this
automorphism gives an actual even conjugator, regardless of the parity of the
coordinate permutation. Thus every conjugator in the final budget belongs to
A₇ itself.

This is the intrinsic group input for the triple-seven exclusion in
Aschbacher–Smith, *The Classification of Quasithin Groups*, combined manuscript
of 1 March 2004, K.1 (printed p.452/PDF p.463). The representation-theoretic
source assembly remains with the Chapter K consumer.
-/

open Equiv Subgroup
open Representation.AlternatingSevenConjugatePair.ElementaryGeometry
namespace alternatingGroup.SevenElementaryGeneration
private abbrev A7 := alternatingGroup (Fin 7)
private def x : A7 := ⟨swap 0 1 * swap 2 3, by rw [Perm.mem_alternatingGroup]; decide +kernel⟩
private def y (t : Bool) : A7 := if t then
  ⟨swap 0 2 * swap 1 3, by rw [Perm.mem_alternatingGroup]; decide +kernel⟩ else
  ⟨swap 0 1 * swap 4 5, by rw [Perm.mem_alternatingGroup]; decide +kernel⟩
private def g (t : Bool) : A7 := if t then
  ⟨swap 1 4 * swap 2 5 * swap 5 3 * swap 3 6,
    by rw [Perm.mem_alternatingGroup]; decide +kernel⟩ else
  ⟨swap 1 2 * swap 3 4 * swap 4 5 * swap 5 6,
    by rw [Perm.mem_alternatingGroup]; decide +kernel⟩
private def letter (t : Bool) (i : Fin 4) : A7 :=
  if i = 0 then x else if i = 1 then y t else if i = 2 then g t * x * (g t)⁻¹
  else g t * y t * (g t)⁻¹
private def seedWord (t : Bool) : List (Fin 4) → A7
  | [] => 1
  | i :: w => letter t i * seedWord t w

private def starWord (t : Bool) (i : Fin 5) : List (Fin 4) :=
  if t then
    ![[2, 0, 2, 1, 0, 2, 1, 2], [2, 0, 2, 1, 2, 1, 0, 2],
      [2, 0, 2, 0], [3, 0, 3, 0], [3, 2, 0, 3, 2, 0]] i
  else
    ![[3, 2, 0, 3, 2, 0, 2], [2, 0, 3, 2, 0, 2, 0, 3], [0, 3, 2, 0, 3, 2],
      [1, 3, 2, 0, 3, 2, 1, 0], [3, 2, 1, 0, 3, 2, 0]] i

private def point (i : Fin 5) : Fin 7 := ⟨i.val + 2, by omega⟩

private theorem seedWord_eq_star : ∀ (t : Bool) (i : Fin 5),
    (seedWord t (starWord t i) : Perm (Fin 7)) = swap 0 1 * swap 0 (point i) := by
  decide +kernel

-- `true` is the regular four-group; `false` is the even three-pair group.
private def model (t : Bool) : Subgroup A7 :=
  (if t then fourTwoElementary else pairElementary).subgroupOf (alternatingGroup (Fin 7))

private theorem x_mem_model : ∀ t, x ∈ model t := by
  intro t
  cases t
  · change (x : S7) ∈ pairElementary
    decide +kernel
  · change (x : S7) ∈ fourTwoElementary
    decide +kernel

private theorem y_mem_model : ∀ t, y t ∈ model t := by
  intro t
  cases t
  · change (y false : S7) ∈ pairElementary
    decide +kernel
  · change (y true : S7) ∈ fourTwoElementary
    decide +kernel

private theorem model_card (t : Bool) : Nat.card (model t) = 4 := by
  rw [← Subgroup.card_map_of_injective (K := model t)
    (alternatingGroup (Fin 7)).subtype_injective, model, subgroupOf_map_subtype]
  cases t
  · exact pairElementary_even_card
  · exact fourTwoElementary_even_card

private theorem seedWord_mem (t : Bool) (H : Subgroup A7)
    (h : ∀ i, letter t i ∈ H) (w : List (Fin 4)) : seedWord t w ∈ H := by
  induction w with
  | nil => exact H.one_mem
  | cons i w ih => exact H.mul_mem (h i) ih

private theorem model_generates (t : Bool) :
    model t ⊔ (model t).map (MulAut.conj (g t)).toMonoidHom = ⊤ := by
  let H := model t ⊔ (model t).map (MulAut.conj (g t)).toMonoidHom
  have h (i : Fin 4) : letter t i ∈ H := by
    fin_cases i
    · exact (show model t ≤ H from le_sup_left) (x_mem_model t)
    · exact (show model t ≤ H from le_sup_left) (y_mem_model t)
    · exact (show (model t).map (MulAut.conj (g t)).toMonoidHom ≤ H from le_sup_right)
        (mem_map_of_mem _ (x_mem_model t))
    · exact (show (model t).map (MulAut.conj (g t)).toMonoidHom ≤ H from le_sup_right)
        (mem_map_of_mem _ (y_mem_model t))
  apply top_unique
  rw [← GLS3.Chapter5.starThreeCycles_closure_eq_top (a := (0 : Fin 7)) (b := 1) (by decide)]
  apply (Subgroup.closure_le _).mpr
  rintro z ⟨i, hi0, hi1, hz⟩
  have hi2 : 2 ≤ i.val := by
    have h0 : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
    have h1 : i.val ≠ 1 := fun h => hi1 (Fin.ext h)
    omega
  let k : Fin 5 := ⟨i.val - 2, by omega⟩
  have hik : point k = i := by apply Fin.ext; simp [point, k]; omega
  have he : z = seedWord t (starWord t k) := by
    apply Subtype.ext
    rw [hz, seedWord_eq_star, hik]
  rw [he]
  exact seedWord_mem t H h _

open Representation.BinaryOffender

private theorem two_conjugates_of_map (A : Subgroup A7) (e : MulAut A7) (k : A7)
    (h : A.map e.toMonoidHom ⊔
      (A.map e.toMonoidHom).map (MulAut.conj k).toMonoidHom = ⊤) :
    A ⊔ A.map (MulAut.conj (e.symm k)).toMonoidHom = ⊤ := by
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.map_sup, Subgroup.map_top_of_surjective _ e.surjective]
  have he : (A.map (MulAut.conj (e.symm k)).toMonoidHom).map e.toMonoidHom =
      (A.map e.toMonoidHom).map (MulAut.conj k).toMonoidHom := by
    rw [map_map, map_map]
    congr 1
    ext a : 1
    change e (e.symm k * a * (e.symm k)⁻¹) = k * e a * k⁻¹
    simp only [map_mul, map_inv, e.apply_symm_apply]
  rw [he]
  exact h

/-- Each elementary four-group in A₇ generates A₇ with one inner conjugate. -/
public theorem four_group_two_conjugates (A : Subgroup (alternatingGroup (Fin 7)))
    (hA : IsElementaryAbelian 2 A) (hc : Nat.card A = 4) :
    ∃ k : alternatingGroup (Fin 7), A ⊔ A.map (MulAut.conj k).toMonoidHom = ⊤ := by
  let _ := hA
  obtain ⟨s, hs⟩ := elementary_conjugate_le
    (IsElementaryAbelian.map (alternatingGroup (Fin 7)).subtype (A := A))
  let e : MulAut A7 := MulAut.conjNormal s
  have he : (A.map e.toMonoidHom).map (alternatingGroup (Fin 7)).subtype =
      (A.map (alternatingGroup (Fin 7)).subtype).map (MulAut.conj s).toMonoidHom := by
    rw [map_map, map_map]
    rfl
  obtain ⟨t, ht⟩ : ∃ t : Bool, A.map e.toMonoidHom ≤ model t := by
    rcases hs with hs | hs
    · refine ⟨false, ?_⟩
      intro a ha
      apply hs
      rw [← he]
      exact mem_map_of_mem _ ha
    · refine ⟨true, ?_⟩
      intro a ha
      apply hs
      rw [← he]
      exact mem_map_of_mem _ ha
  have hb : A.map e.toMonoidHom = model t :=
    Subgroup.eq_of_le_of_card_ge ht (by
      rw [model_card, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hc])
  exact ⟨e.symm (g t), two_conjugates_of_map A e (g t) (by
    rw [hb]
    exact model_generates t)⟩

/-- Nontrivial elementary two-subgroups of A₇ admit generating inner conjugates
whose number times their binary rank is at most four. -/
public theorem elementaryConjugateBudget :
    ElementaryConjugateBudget (alternatingGroup (Fin 7)) 4 := by
  intro A hA
  let _ : IsElementaryAbelian 2 A := hA.2
  have hc : Nat.card A ≤ 4 := by
    have h := elementary_even_card_le
      (IsElementaryAbelian.map (alternatingGroup (Fin 7)).subtype (A := A))
      (Subgroup.map_subtype_le A)
    rwa [Subgroup.card_map_of_injective (alternatingGroup (Fin 7)).subtype_injective] at h
  have hr : rank A ≤ 2 := by
    rw [hA.card_eq_two_pow_rank] at hc
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
  by_cases h1 : rank A = 1
  · obtain ⟨a, ha, ha1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
    obtain ⟨u, v, huv⟩ := SevenInvolutionGeneration.three_conjugates_generate a ha1
      (elemPow_eq_one_of_isElementaryAbelian a ha)
    let c : Fin 3 → A7 := ![1, u, v]
    let J := ⨆ i, A.map (MulAut.conj (c i)).toMonoidHom
    refine ⟨3, c, by rw [h1]; decide, top_unique ?_⟩
    change ⊤ ≤ J
    have hz : zpowers a ≤ A := zpowers_le.mpr ha
    have hzero : A ≤ J := by
      intro b hb
      apply (le_iSup (fun i => A.map (MulAut.conj (c i)).toMonoidHom) (0 : Fin 3))
      refine ⟨b, hb, ?_⟩
      change 1 * b * (1 : A7)⁻¹ = b
      simp
    have hu : zpowers (u * a * u⁻¹) ≤ J := by
      change zpowers ((MulAut.conj u).toMonoidHom a) ≤ J
      rw [← MonoidHom.map_zpowers]
      exact (Subgroup.map_mono hz).trans
        (le_iSup (fun i => A.map (MulAut.conj (c i)).toMonoidHom) (1 : Fin 3))
    have hv : zpowers (v * a * v⁻¹) ≤ J := by
      change zpowers ((MulAut.conj v).toMonoidHom a) ≤ J
      rw [← MonoidHom.map_zpowers]
      exact (Subgroup.map_mono hz).trans
        (le_iSup (fun i => A.map (MulAut.conj (c i)).toMonoidHom) (2 : Fin 3))
    rw [← huv]
    exact sup_le (sup_le (hz.trans hzero) hu) hv
  · have h2 : rank A = 2 := by
      have := hA.rank_pos
      omega
    obtain ⟨k, hk⟩ := four_group_two_conjugates A hA.2 (by
      rw [hA.card_eq_two_pow_rank, h2]; decide)
    let c : Fin 2 → A7 := ![1, k]
    let J := ⨆ i, A.map (MulAut.conj (c i)).toMonoidHom
    refine ⟨2, c, by omega, top_unique ?_⟩
    change ⊤ ≤ J
    have hzero : A ≤ J := by
      intro b hb
      apply (le_iSup (fun i => A.map (MulAut.conj (c i)).toMonoidHom) (0 : Fin 2))
      refine ⟨b, hb, ?_⟩
      change 1 * b * (1 : A7)⁻¹ = b
      simp
    rw [← hk]
    exact sup_le hzero
      (le_iSup (fun i => A.map (MulAut.conj (c i)).toMonoidHom) (1 : Fin 2))
end alternatingGroup.SevenElementaryGeneration
