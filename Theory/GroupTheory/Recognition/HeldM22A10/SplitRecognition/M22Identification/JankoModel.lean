module

public import Theory.Mathieu.M22.Properties.Order
public import Theory.GroupTheory.WordSubgroup
import Mathlib.Tactic.FinCases

/-!
# Janko's terminal permutation group and the Steiner Mathieu group

The permutations `ell`, `m`, and `n2` are those on printed p.18 of
Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), 1--19, DOI 10.1016/0021-8693(68)90002-1.
Labels are interpreted modulo 22, as in the existing Atlas generators.

An explicit relabeling conjugates their generated subgroup to the Atlas
subgroup. Five word identities prove the two inclusions by kernel reduction.
The previously proved equality of the Atlas and even Steiner groups then
gives an actual multiplicative equivalence with `Sporadic.Mathieu.M22`.
This is a comparison of concrete models, not recognition of an arbitrary
group from its centralizer or order.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.JankoModel

open Subgroup Sporadic.Mathieu

/-- Janko's fixed-point-free element of order eleven. -/
@[expose] public def ell : Equiv.Perm (Fin 22) :=
  List.formPerm [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] *
    List.formPerm [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

/-- Janko's element of order five normalizing the eleven-cycle subgroup. -/
@[expose] public def m : Equiv.Perm (Fin 22) :=
  List.formPerm [1, 4, 5, 9, 3] * List.formPerm [2, 8, 10, 7, 6] *
    List.formPerm [12, 15, 16, 20, 14] * List.formPerm [13, 19, 21, 18, 17]

/-- The surviving second candidate for the order-four generator on p.18. -/
@[expose] public def n2 : Equiv.Perm (Fin 22) :=
  Equiv.swap 11 22 * Equiv.swap 8 14 * List.formPerm [4, 5, 3, 9] *
    List.formPerm [13, 18, 17, 19] * List.formPerm [2, 16, 10, 15] *
    List.formPerm [7, 20, 6, 12]

/-- The concrete three-generator subgroup in Janko's conclusion. -/
@[expose] public def model : Subgroup (Equiv.Perm (Fin 22)) :=
  closure {ell, m, n2}

/-- A point relabeling from Janko's group to the repository's Atlas group. -/
@[expose] public def relabeling : Equiv.Perm (Fin 22) :=
  List.formPerm [2, 14, 20, 9, 19, 4, 7, 11, 10, 8, 18, 13, 12, 6, 15, 5,
    17, 21, 3, 16, 22]

private def atlasGen : Fin 4 → Equiv.Perm (Fin 22)
  | 0 => m22GeneratorA
  | 1 => m22GeneratorB
  | 2 => m22GeneratorA⁻¹
  | 3 => m22GeneratorB⁻¹

private def jankoGen : Fin 6 → Equiv.Perm (Fin 22)
  | 0 => ell
  | 1 => m
  | 2 => n2
  | 3 => ell⁻¹
  | 4 => m⁻¹
  | 5 => n2⁻¹

private theorem eval_mem {k : ℕ} (gen : Fin k → Equiv.Perm (Fin 22))
    (S : Subgroup (Equiv.Perm (Fin 22))) (h : ∀ i, gen i ∈ S)
    (w : List (Fin k)) : evalWord gen w ∈ S := by
  induction w with
  | nil => exact S.one_mem
  | cons i w ih => exact S.mul_mem (h i) ih

private theorem atlasGen_mem (i : Fin 4) : atlasGen i ∈ m22Atlas := by
  have ha : m22GeneratorA ∈ m22Atlas := subset_closure (by simp)
  have hb : m22GeneratorB ∈ m22Atlas := subset_closure (by simp)
  fin_cases i
  · exact ha
  · exact hb
  · exact m22Atlas.inv_mem ha
  · exact m22Atlas.inv_mem hb

private theorem jankoGen_mem (i : Fin 6) : jankoGen i ∈ model := by
  have hl : ell ∈ model := subset_closure (by simp)
  have hm : m ∈ model := subset_closure (by simp)
  have hn : n2 ∈ model := subset_closure (by simp)
  fin_cases i
  · exact hl
  · exact hm
  · exact hn
  · exact model.inv_mem hl
  · exact model.inv_mem hm
  · exact model.inv_mem hn

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

private theorem ell_word : (MulAut.conj relabeling) ell =
    evalWord atlasGen
      [1, 1, 2, 1, 2, 3, 3, 2, 2, 3, 2, 3, 3, 2, 1, 2, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 2, 3, 3, 2, 3, 2, 3, 0, 1, 0, 3, 0, 3, 0] := by
  decide +kernel

private theorem m_word : (MulAut.conj relabeling) m =
    evalWord atlasGen
      [3, 3, 3, 3, 2, 3, 3, 3, 3, 2, 3, 2, 3, 2, 3, 3, 2, 1, 2, 1, 2, 3, 0, 1, 0, 1, 1, 0, 3, 0, 3, 0, 1, 0, 1, 1, 0, 3, 0] := by
  decide +kernel

private theorem n2_word : (MulAut.conj relabeling) n2 =
    evalWord atlasGen
      [2, 3, 3, 2, 2, 3, 2, 3, 2, 3, 2, 3, 3, 2, 2, 1, 2, 3, 2, 1, 2, 3, 2, 2, 1, 2, 1, 2, 3, 2, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 0, 1, 0, 1, 1, 2, 3, 2, 1] := by
  decide +kernel

private theorem a_word : (MulAut.conj relabeling).symm m22GeneratorA =
    evalWord jankoGen
      [3, 5, 3, 3, 5, 3, 4, 3, 3, 5, 3, 2, 4, 3, 2, 4, 3, 3, 4, 2, 3, 5, 1] := by
  decide +kernel

private theorem b_word : (MulAut.conj relabeling).symm m22GeneratorB =
    evalWord jankoGen
      [0, 1, 5, 0, 1, 5, 0, 2, 0, 5, 0, 2, 3, 2, 1, 2, 3, 1, 0, 4] := by
  decide +kernel

/-- Relabeling conjugates Janko's generated subgroup onto the Atlas subgroup. -/
public theorem map_model_eq_atlas :
    model.map (MulAut.conj relabeling).toMonoidHom = m22Atlas := by
  apply le_antisymm
  · apply map_le_iff_le_comap.mpr
    rw [model, closure_le]
    intro g hg
    change (MulAut.conj relabeling) g ∈ m22Atlas
    rcases hg with rfl | rfl | rfl
    · rw [ell_word]
      exact eval_mem atlasGen m22Atlas atlasGen_mem _
    · rw [m_word]
      exact eval_mem atlasGen m22Atlas atlasGen_mem _
    · rw [n2_word]
      exact eval_mem atlasGen m22Atlas atlasGen_mem _
  · rw [m22Atlas, closure_le]
    intro g hg
    change g ∈ model.map (MulAut.conj relabeling).toMonoidHom
    rw [mem_map_equiv]
    rcases hg with rfl | rfl
    · rw [a_word]
      exact eval_mem jankoGen model jankoGen_mem _
    · rw [b_word]
      exact eval_mem jankoGen model jankoGen_mem _

/-- The concrete endpoint of Janko's proof is the genuine Steiner Mathieu group. -/
public noncomputable def equivM22 : model ≃* M22 :=
  ((MulAut.conj relabeling).subgroupMap model).trans
    (MulEquiv.subgroupCongr (map_model_eq_atlas.trans m22Atlas_eq_M22))

/-- The order of the concrete endpoint, transported along the checked comparison. -/
public theorem model_card : Nat.card model = 443520 :=
  (Nat.card_congr equivM22.toEquiv).trans m22_order

/-- Left conjugation is used for the Lean permutation convention. -/
public theorem m_conjugates_ell : m * ell * m⁻¹ = ell ^ 4 := by
  decide +kernel

/-- The second source normalizer relation in the same convention. -/
public theorem n2_conjugates_m : n2 * m * n2⁻¹ = m ^ 2 := by
  decide +kernel


/-- The fourth candidate for the order-four generator on p.18. -/
@[expose] public def n4 : Equiv.Perm (Fin 22) :=
  Equiv.swap 11 22 * Equiv.swap 1 21 * List.formPerm [2, 10, 8, 6] *
    List.formPerm [12, 14, 16, 20] * List.formPerm [4, 17, 3, 13] *
    List.formPerm [5, 19, 9, 18]

/-- The relabeling between the two surviving candidates. The first long cycle
of the printed alpha on p.18 has `13` where `3` is needed, repeating `13`.
The three checked identities below verify the correction. -/
@[expose] public def fourthRelabeling : Equiv.Perm (Fin 22) :=
  Equiv.swap 11 22 * List.formPerm [1, 14, 9, 16, 4, 12, 3, 20, 5, 15] *
    List.formPerm [2, 17, 7, 21, 8, 13, 6, 18, 10, 19]

public theorem fourthRelabeling_ell :
    (MulAut.conj fourthRelabeling) ell = ell ^ 3 := by
  decide +kernel

public theorem fourthRelabeling_m : (MulAut.conj fourthRelabeling) m = m := by
  decide +kernel

public theorem fourthRelabeling_n4 : (MulAut.conj fourthRelabeling) n4 = n2 := by
  decide +kernel

/-- The fourth candidate generates the same group after relabeling. -/
public theorem map_fourth_model_eq_model :
    (closure ({ell, m, n4} : Set (Equiv.Perm (Fin 22)))).map
      (MulAut.conj fourthRelabeling).toMonoidHom = model := by
  let Q := closure ({ell, m, n4} : Set (Equiv.Perm (Fin 22)))
  let f := (MulAut.conj fourthRelabeling).toMonoidHom
  have hl : ell ∈ Q := subset_closure (by simp)
  have hm : m ∈ Q := subset_closure (by simp)
  have hn : n4 ∈ Q := subset_closure (by simp)
  have hl' : ell ^ 3 ∈ Q.map f := fourthRelabeling_ell ▸ mem_map_of_mem f hl
  have hm' : m ∈ Q.map f := fourthRelabeling_m ▸ mem_map_of_mem f hm
  have hn' : n2 ∈ Q.map f := fourthRelabeling_n4 ▸ mem_map_of_mem f hn
  have hl4 : (ell ^ 3) ^ 4 = ell := by decide +kernel
  apply le_antisymm
  · apply map_le_iff_le_comap.mpr
    rw [closure_le]
    intro g hg
    change (MulAut.conj fourthRelabeling) g ∈ model
    rcases hg with rfl | rfl | rfl
    · rw [fourthRelabeling_ell]
      exact model.pow_mem (subset_closure (by simp)) _
    · rw [fourthRelabeling_m]
      exact subset_closure (by simp)
    · rw [fourthRelabeling_n4]
      exact subset_closure (by simp)
  · rw [model, closure_le]
    intro g hg
    change g ∈ Q.map f
    rcases hg with rfl | rfl | rfl
    · exact hl4 ▸ (Q.map f).pow_mem hl' 4
    · exact hm'
    · exact hn'

end Theory.GroupTheory.HeldM22A10.M22Identification.JankoModel
