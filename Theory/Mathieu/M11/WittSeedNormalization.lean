module

public import Theory.Mathieu.M11.WittCompletionSeed
public import Theory.GroupTheory.SteinerSystem.Transport
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.FinCases

/-!
# Normalizing the four blocks through a Witt-design triple

For any `S(4,5,11)`, the blocks containing a fixed triple have disjoint
two-point residuals and cover its eight-point complement. There are therefore
four such blocks. Enumerating these blocks and their two residual points gives
an injective labeling of eight points; extend it to a permutation of all eleven
points. Its remaining three points form the normalized triple.

This is the elementary triple-residue argument from the Steiner-system axioms;
no recognition or uniqueness theorem for the Witt design is used.
-/

open Theory.GroupTheory
open scoped Pointwise

namespace Sporadic.Mathieu

/-- Blocks through any fixed triple partition its complement into four pairs. -/
public theorem m11_triple_residual_partition (D : SteinerSystem (Fin 11) 4 5)
    (T : Finset (Fin 11)) (hT : T.card = 3) :
    (D.blocks.filter (T ⊆ ·)).card = 4 ∧
    (∀ B ∈ D.blocks.filter (T ⊆ ·), (B \ T).card = 2) ∧
    (↑(D.blocks.filter (T ⊆ ·)) : Set (Finset (Fin 11))).PairwiseDisjoint (· \ T) ∧
    (D.blocks.filter (T ⊆ ·)).biUnion (· \ T) = Finset.univ \ T := by
  obtain ⟨hpair, hdisj, hcover⟩ := D.residual_partition T hT
  refine ⟨?_, hpair, hdisj, hcover⟩
  have hcount := congrArg Finset.card hcover
  rw [Finset.card_biUnion hdisj, Finset.card_sdiff_of_subset (Finset.subset_univ T),
    Finset.card_univ, Fintype.card_fin, hT] at hcount
  have hsum : ∑ B ∈ D.blocks.filter (T ⊆ ·), (B \ T).card =
      (D.blocks.filter (T ⊆ ·)).card * 2 := by
    calc
      _ = ∑ _B ∈ D.blocks.filter (T ⊆ ·), 2 :=
        Finset.sum_congr rfl (fun B hB => hpair B hB)
      _ = _ := by simp
  rw [hsum] at hcount
  omega

private def triple : Finset (Fin 11) := {0, 1, 2}

private def pairLabel (a : Fin 4 × Fin 2) : Fin 11 :=
  ⟨3 + 2 * a.1.val + a.2.val, by omega⟩

private theorem pairLabel_injective : Function.Injective pairLabel := by
  decide +kernel

private theorem pairLabel_not_mem (a : Fin 4 × Fin 2) : pairLabel a ∉ triple := by
  revert a
  decide +kernel

private theorem pairLabel_covers : ∀ x : Fin 11, x ∉ triple →
    ∃ a : Fin 4 × Fin 2, pairLabel a = x := by
  decide +kernel

/-- Every `S(4,5,11)` can be relabeled to contain the four-block completion seed. -/
public theorem exists_relabel_m11CompletionSeed (D : SteinerSystem (Fin 11) 4 5) :
    ∃ (e : Equiv.Perm (Fin 11)) (D' : SteinerSystem (Fin 11) 4 5),
      D'.blocks = e • D.blocks ∧ m11CompletionSeed ⊆ D'.blocks := by
  classical
  obtain ⟨hfour, hpair, hdisj, _⟩ :=
    m11_triple_residual_partition D triple (by decide +kernel)
  let F := D.blocks.filter (triple ⊆ ·)
  let q : Fin 4 ≃ F := (Finset.equivFinOfCardEq hfour).symm
  let p (i : Fin 4) : Fin 2 ≃ ↥((q i).val \ triple) :=
    (Finset.equivFinOfCardEq (hpair (q i).val (q i).property)).symm
  let f (a : Fin 4 × Fin 2) : Fin 11 := (p a.1 a.2).val
  have hfnot (a : Fin 4 × Fin 2) : f a ∉ triple :=
    (Finset.mem_sdiff.mp (p a.1 a.2).property).2
  have hfinj : Function.Injective f := by
    rintro ⟨i, x⟩ ⟨j, y⟩ hxy
    have hij : i = j := by
      apply q.injective
      apply Subtype.ext
      by_contra hne
      have hd := hdisj (q i).property (q j).property hne
      apply Finset.disjoint_left.mp hd (p i x).property
      change f (i, x) ∈ (q j).val \ triple
      rw [hxy]
      exact (p j y).property
    subst j
    have hxy' : x = y := (p i).injective (Subtype.ext hxy)
    exact Prod.ext rfl hxy'
  obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair f pairLabel hfinj pairLabel_injective
  have hetriple : e • triple = triple := by
    apply Finset.eq_of_subset_of_card_le ?_ (by rw [Finset.card_smul_finset])
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_smul_finset.mp hx
    by_contra hnot
    obtain ⟨a, ha⟩ := pairLabel_covers (e y) hnot
    have hay : f a = y := e.injective ((he a).trans ha)
    exact hfnot a (hay.symm ▸ hy)
  have hepair (i : Fin 4) : e • ((q i).val \ triple) =
      {pairLabel (i, 0), pairLabel (i, 1)} := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_smul_finset.mp hx
      obtain ⟨j, hj⟩ := (p i).surjective ⟨y, hy⟩
      have hfy : f (i, j) = y := congrArg Subtype.val hj
      change e y ∈ _
      rw [← hfy, he]
      fin_cases j <;> simp
    · intro hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_smul_finset.mpr
          ⟨f (i, 0), (p i 0).property, he (i, 0)⟩
      · exact Finset.mem_smul_finset.mpr
          ⟨f (i, 1), (p i 1).property, he (i, 1)⟩
  have heblock (i : Fin 4) :
      triple ∪ {pairLabel (i, 0), pairLabel (i, 1)} ∈ (D.relabel e).blocks := by
    have hqi := Finset.mem_filter.mp (q i).property
    have hblock : e • (q i).val =
        triple ∪ {pairLabel (i, 0), pairLabel (i, 1)} := by
      calc
        e • (q i).val = e • (triple ∪ ((q i).val \ triple)) :=
          congrArg (e • ·) (Finset.union_sdiff_of_subset hqi.2).symm
        _ = _ := by rw [Finset.smul_finset_union, hetriple, hepair]
    rw [← hblock, SteinerSystem.relabel_blocks]
    exact Finset.smul_mem_smul_finset hqi.1
  refine ⟨e, D.relabel e, rfl, ?_⟩
  have hseed : m11CompletionSeed =
      Finset.univ.image (fun i : Fin 4 =>
        triple ∪ {pairLabel (i, 0), pairLabel (i, 1)}) := by
    decide +kernel
  rw [hseed]
  intro B hB
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hB
  exact heblock i

end Sporadic.Mathieu
