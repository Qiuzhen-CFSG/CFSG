module
public import Theory.Representation.BinarySevenCode.WeightTwoSplitting

/-!
# Swaps in the Sylow action at a weight-two point

A permutation fixing the five complementary letters is either the identity
or the support-pair swap. A Sylow two-subgroup of S₇ stabilizing the pair
also contains a swap of complementary letters: place such an involution
inside its Sylow subgroup within the word stabilizer. These two facts let
maximum elementary subgroup transport detect Thompson movement on A₅.

Source: Aschbacher--Smith, Lemma 12.3.7(2), printed p.809.
-/
@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
namespace BinarySevenCode.WeightTwoGeometry

theorem support_swap_image_le (w : EvenWord) (i j : Fin 7) (hij : i ≠ j)
    (hw : support w = {i,j}) (g : symmetricStabilizer w)
    (hg : ∀ k : Complement w, g.val k = k) :
    g.val = 1 ∨ g.val = Equiv.swap i j := by
  have hi := (stabilizer_mem_support w g i).mpr (hw ▸ (by simp : i ∈ ({i,j} : Finset (Fin 7))))
  have hj := (stabilizer_mem_support w g j).mpr (hw ▸ (by simp : j ∈ ({i,j} : Finset (Fin 7))))
  rw [hw] at hi hj
  simp only [Finset.mem_insert,Finset.mem_singleton] at hi hj
  have hne := g.val.injective.ne hij
  have hother (k : Fin 7) (hki : k ≠ i) (hkj : k ≠ j) : g.val k = k := by
    exact hg ⟨k,Finset.mem_compl.mpr (by rw [hw]; simpa using And.intro hki hkj)⟩
  rcases hi with hi | hi
  · left
    have hj' : g.val j = j := hj.resolve_left (fun hh => hne (hi.trans hh.symm))
    apply Equiv.ext
    intro k
    change g.val k = k
    by_cases hki : k = i
    · simpa only [hki] using hi
    by_cases hkj : k = j
    · simpa only [hkj] using hj'
    exact hother k hki hkj
  · right
    have hj' : g.val j = i := hj.resolve_right (fun hh => hne (hi.trans hh.symm))
    apply Equiv.ext
    intro k
    by_cases hki : k = i
    · simp only [hki,hi,Equiv.swap_apply_left]
    by_cases hkj : k = j
    · simp only [hkj,hj',Equiv.swap_apply_right]
    rw [hother k hki hkj,Equiv.swap_apply_of_ne_of_ne hki hkj]

theorem sylow_contains_complement_swap (w : EvenWord) (hw : weight w.val = 2)
    (Q : Sylow 2 (Equiv.Perm (Fin 7)))
    (hQC : (Q : Subgroup (Equiv.Perm (Fin 7))) ≤ symmetricStabilizer w) :
    ∃ i j : Complement w, i ≠ j ∧ Equiv.swap i.val j.val ∈ Q := by
  have hn : Nontrivial (Complement w) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [complement_card w hw]; decide)
  obtain ⟨i,j,hij⟩ := exists_pair_ne (Complement w)
  have ht : Equiv.swap i.val j.val ∈ symmetricStabilizer w := by
    rw [WeightTwoGeometry.mem_symmetricStabilizer]
    apply Subtype.ext
    funext k
    change w.val ((Equiv.swap i.val j.val).symm k) = w.val k
    have hi : w.val i.val = 0 := by
      have h := Finset.mem_compl.mp i.property
      simpa only [support,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using h
    have hj : w.val j.val = 0 := by
      have h := Finset.mem_compl.mp j.property
      simpa only [support,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using h
    simp only [Equiv.symm_swap,Equiv.swap_apply_def]
    split_ifs <;> simp_all
  let t : symmetricStabilizer w := ⟨Equiv.swap i.val j.val,ht⟩
  have hp : IsPGroup 2 (zpowers t) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers]
    apply orderOf_dvd_of_pow_eq_one
    exact Subtype.ext (by change (Equiv.swap i.val j.val)^2 = 1; simp [pow_two]))
  obtain ⟨R,hR⟩ := hp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (symmetricStabilizer w) R (Q.subtype hQC)
  have htR : g * t * g⁻¹ ∈ Q.subtype hQC := by
    rw [← hg]
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom (hR (mem_zpowers t))
  let a := complementPermutation w g i
  let b := complementPermutation w g j
  refine ⟨a,b,(complementPermutation w g).injective.ne hij,?_⟩
  have he : Equiv.swap a.val b.val = g.val * t.val * g.val⁻¹ :=
    Equiv.swap_apply_apply g.val i.val j.val
  rw [he]
  exact htR

end BinarySevenCode.WeightTwoGeometry
