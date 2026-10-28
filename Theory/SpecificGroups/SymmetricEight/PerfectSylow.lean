module
public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.TreeSylow
public import Theory.GroupTheory.Commutator.PerfectSmallIndex
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.Perm.Closure

/-!
# Perfect subgroups normalized by a full Sylow of S₈

A seven-cycle fixes a unique letter. Every full Sylow two-subgroup contains
a transposition through that letter, as seen in the binary-tree Sylow.
Conjugating this swap by the cycle gives all star transpositions, hence
S₈. Thus a perfect subgroup with a seven-element normalized by the full
Sylow is normal in S₈ and equals A₈.

This is the permutation-group comparison used in Aschbacher--Smith
12.9.4, printed p.859, where the original point residual has an L₃(2)
quotient and cannot equal A₈. The use of a full Sylow is essential.
-/

public noncomputable section
open Subgroup Equiv MulAction
namespace Theory.SpecificGroups.SymmetricEight.PerfectSylow
local notation "S8" => Perm (Fin 8)
open A6ShadowTwoLocals in
/-- Every point lies in a transposition of a full Sylow two-subgroup of S₈. -/
theorem sylow_contains_incident_swap (S : Sylow 2 S8) (z : Fin 8) :
    ∃ w, z ≠ w ∧ swap z w ∈ (S : Subgroup S8) := by
  let U : Sylow 2 S8 := Sylow.ofCard treeGroup (by
    rw [card_treeGroup,Nat.card_perm,Nat.card_fin]
    decide +kernel)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq S8 U S
  have ht : ∀ z : Fin 8, ∃ (i : Fin 7) (w : Fin 8), z ≠ w ∧ treeGenerator i = swap z w := by
    decide +kernel
  obtain ⟨i,w,hw,hi⟩ := ht (g⁻¹ z)
  refine ⟨g w,?_,?_⟩
  · intro he
    apply hw
    simpa only [Perm.inv_def, symm_apply_apply] using congrArg (fun a => g.symm a) he
  · rw [←hg]
    change swap z (g w) ∈ (U : Subgroup S8).map (MulAut.conj g).toMonoidHom
    have hm := mem_map_of_mem (MulAut.conj g).toMonoidHom (show treeGenerator i ∈ (U : Subgroup S8) from treeGenerator_mem i)
    change g * treeGenerator i * g⁻¹ ∈ _ at hm
    rw [hi,mul_swap_eq_swap_mul,mul_inv_cancel_right] at hm
    simpa only [Perm.inv_def,apply_symm_apply] using hm

private theorem cycle_fixed_swap_generate (b : S8) (hb : b.IsCycle)
    (hc : b.support.card = 7) (z w : Fin 8) (hz : b z = z) (hw : z ≠ w)
    (D : Subgroup S8) (hD : b ∈ D) (hs : swap z w ∈ D) : D = ⊤ := by
  classical
  have hfixed (y : Fin 8) (hy : y ≠ z) : b y ≠ y := by
    intro he
    have hsub : b.support ⊆ Finset.univ \ {z,y} := by
      intro a ha
      simp only [Finset.mem_sdiff,Finset.mem_univ,Finset.mem_insert,Finset.mem_singleton,
        true_and,not_or]
      exact ⟨fun h => (Perm.mem_support.mp ha) (h.symm ▸ hz),
        fun h => (Perm.mem_support.mp ha) (h.symm ▸ he)⟩
    have hh := Finset.card_le_card hsub
    have hcard : (Finset.univ \ {z,y} : Finset (Fin 8)).card = 6 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      simp [Finset.card_pair hy.symm]
    rw [hc,hcard] at hh
    omega
  have hpow : ∀ k : ℕ, (b^k) z = z := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => simpa only [pow_succ',Perm.mul_apply,ih] using hz
  have hstar (y : Fin 8) : swap z y ∈ D := by
    by_cases he : y = z
    · rw [he,swap_self]; exact D.one_mem
    obtain ⟨k,hk⟩ := hb.exists_pow_eq (hfixed w hw.symm) (hfixed y he)
    have hm := D.mul_mem (D.mul_mem (D.pow_mem hD k) hs) (D.inv_mem (D.pow_mem hD k))
    simpa only [mul_swap_eq_swap_mul,mul_inv_cancel_right,hpow,hk] using hm
  have hall (x y : Fin 8) : swap x y ∈ D := by
    by_cases hyz : y = z
    · rw [hyz,swap_comm]; exact hstar x
    by_cases hyx : y = x
    · rw [hyx,swap_self]; exact D.one_mem
    rw [← swap_mul_swap_mul_swap hyz hyx,swap_comm y z]
    exact D.mul_mem (D.mul_mem (hstar x) (hstar y)) (hstar x)
  rw [eq_top_iff,←Perm.closure_isSwap,closure_le]
  rintro a ⟨x,y,_,rfl⟩
  exact hall x y

/-- A perfect subgroup with a seven-element normalized by a full Sylow
of S₈ is the whole alternating group. -/
theorem eq_alternating_of_seven_dvd (B : Subgroup S8) [Group.IsPerfect B]
    (S : Sylow 2 S8) (hSB : (S : Subgroup S8) ≤ normalizer (B : Set S8))
    (hd : 7 ∣ Nat.card B) : B = alternatingGroup (Fin 8) := by
  classical
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨b,hb⟩ := exists_prime_orderOf_dvd_card' (G := B) 7 hd
  have hb' : orderOf (b : S8) = 7 := (orderOf_coe b).trans hb
  have hc : (b : S8).IsCycle := Perm.isCycle_of_prime_order' (hb' ▸ (by decide : Nat.Prime 7)) (by rw [hb']; decide)
  have hcard : (b : S8).support.card = 7 := hc.orderOf.symm.trans hb'
  have hz : ∃ z : Fin 8, (b : S8) z = z := by
    by_contra! hn
    have he : (b : S8).support = Finset.univ := by
      ext z; simp only [Perm.mem_support,Finset.mem_univ,iff_true]; exact hn z
    rw [he] at hcard
    norm_num at hcard
  obtain ⟨z,hz⟩ := hz
  obtain ⟨w,hw,hs⟩ := sylow_contains_incident_swap S z
  have hn : normalizer (B : Set S8) = ⊤ :=
    cycle_fixed_swap_generate b hc hcard z w hz hw _ (B.le_normalizer b.property) (hSB hs)
  let : B.Normal := normalizer_eq_top_iff.mp hn
  have hne : B ≠ ⊥ := by
    intro he; rw [he,card_bot] at hd; norm_num at hd
  let : Nontrivial B := (nontrivial_iff_ne_bot B).mpr hne
  exact le_antisymm (le_of_isPerfect_of_index_le_four B _ (by rw [alternatingGroup.index_eq_two]; decide))
    (Perm.alternatingGroup_le_of_normal (by simp) inferInstance)

end Theory.SpecificGroups.SymmetricEight.PerfectSylow
