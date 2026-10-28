module

public import Theory.Representation.BinaryPermutation

/-!
# Faithfulness of the binary natural permutation action

In degree at least five, a coordinate permutation fixing the natural module
fixes every pair of coordinates. The difference of two pair vectors has
support of size at most four, so it cannot be a nonzero constant vector.
Fixing all pairs forces the permutation to be the identity.

This generalizes the six-part proof in
`MathieuCode.sextetNatural_faithful`, without importing the Mathieu model.
Source: Aschbacher–Smith, §B.3, the natural deleted permutation module;
the faithful six-letter action is used in K.1.1, printed p.452.
-/

public section
namespace BinaryPermutation
variable (Ω : Type*) [Fintype Ω]

/-- The natural symmetric-group action is faithful in degree at least five. -/
theorem naturalRepresentation_injective (hn : 5 ≤ Fintype.card Ω) :
    Function.Injective (naturalRepresentation Ω) := by
  classical
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  apply Equiv.ext
  intro i
  by_contra hgi
  change g i ≠ i at hgi
  have hj : ({i, g i} : Finset Ω).card < Fintype.card Ω :=
    lt_of_le_of_lt Finset.card_le_two (by omega)
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({i, g i} : Finset Ω).card < Finset.univ.card by simpa using hj)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
  let u : Full Ω := Pi.single i 1 + Pi.single j 1
  have hu : u ∈ core Ω := by
    simp [u, mem_core, Finset.sum_add_distrib, CharTwo.add_self_eq_zero]
  let x : natural Ω := ⟨(constants Ω).mkQ u, u, hu, rfl⟩
  have he := congrArg Subtype.val (LinearMap.congr_fun hg x)
  have hm : representation Ω g u - u ∈ constants Ω :=
    (Submodule.Quotient.eq _).mp he
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
  have hperm (a : Ω) : representation Ω g (Pi.single a 1) = Pi.single (g a) 1 := by
    ext k
    simp [Pi.single_apply, Equiv.symm_apply_eq]
  rw [show representation Ω g u = Pi.single (g i) 1 + Pi.single (g j) 1 from
    (map_add _ _ _).trans (congrArg₂ (· + ·) (hperm i) (hperm j))] at hc
  have hk : ({i, j, g i, g j} : Finset Ω).card < Fintype.card Ω :=
    lt_of_le_of_lt Finset.card_le_four (by omega)
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({i, j, g i, g j} : Finset Ω).card < Finset.univ.card by simpa using hk)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  have hc0 : c = 0 := by
    have he := congrFun hc k
    simpa [u, allOne, Pi.single_apply, hk.1, hk.2.1, hk.2.2.1, hk.2.2.2] using he
  have he := congrFun hc (g i)
  have hij : i ≠ j := Ne.symm hj.1
  simp [hc0, u, allOne, hgi, Ne.symm hj.2, hij] at he

end BinaryPermutation
