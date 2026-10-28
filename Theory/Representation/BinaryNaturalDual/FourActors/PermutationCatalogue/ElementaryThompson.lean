module

public import Theory.Representation.BinaryNaturalDual.FourActors.PermutationCatalogue.Representatives
public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.TreeWreathModel

/-!
# The unique largest elementary subgroup of the even tree Sylow

The even part of the binary-tree Sylow has 28 elements whose square is one.
Sixteen lie in the two-block Klein group. Each of the twelve remaining
involutions commutes with precisely twelve of those 28 elements. Consequently
an elementary subgroup leaving the Klein group has order at most twelve;
the unique elementary subgroup of order at least sixteen is the marked A₀.

The finite checks concern only the 128 existing tree normal forms, and then
28 candidates for each of twelve centralizers. An injection from an arbitrary
elementary subgroup into these candidates turns the checks into order bounds.
The specified eight-point equivalence transports the actual tree Sylow and
these bounds to Aut(GL₄(2)). The source's elementary Thompson construction
is applied separately in the Chapter H adapter.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.3(3),
printed pp.391–392, PDF pp.402–403.
-/

public section

namespace BinaryNaturalDual.FourActors.PermutationCatalogue
open Equiv Subgroup
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
open Theory.SpecificGroups.SymmetricEight.FourBlockCoreAction
open scoped IsMulCommutative

private def evenInvolutionIndices : Finset (Fin 128) :=
  {0, 3, 5, 6, 9, 10, 12, 15, 16, 19, 28, 31, 32, 35, 44, 47,
    48, 51, 60, 63, 64, 69, 74, 79, 112, 118, 121, 127}

private def outsideIndices : Finset (Fin 128) :=
  {5, 6, 9, 10, 64, 69, 74, 79, 112, 118, 121, 127}

set_option maxRecDepth 10000 in
private theorem even_involution_indices : ∀ i,
    (treeWord i).sign = 1 → treeWord i ^ 2 = 1 → i ∈ evenInvolutionIndices := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem remaining_indices_klein : ∀ i ∈ evenInvolutionIndices,
    i ∉ outsideIndices → ∃ a b, treeWord i = kleinPerm a b := by
  decide +kernel

private def commutingIndices (i : Fin 128) : Finset (Fin 128) :=
  evenInvolutionIndices.filter fun j => treeWord j * treeWord i = treeWord i * treeWord j

set_option maxRecDepth 10000 in
private theorem commuting_indices_card :
    ∀ i ∈ outsideIndices, (commutingIndices i).card = 12 := by
  decide +kernel

/-- An elementary subgroup of the even tree Sylow leaving A₀ has order at most twelve. -/
theorem permutation_even_tree_card_le_twelve (E : Subgroup S) [IsElementaryAbelian 2 E]
    (hle : E ≤ treeGroup ⊓ alternatingGroup (Fin 8))
    (hne : ¬ E ≤ permutationA0) : Nat.card E ≤ 12 := by
  classical
  rw [permutationA0_eq_kleinGroup] at hne
  obtain ⟨x, hxE, hxK⟩ : ∃ x ∈ E, x ∉ kleinGroup := by
    by_contra hn
    apply hne
    intro x hx
    by_contra hk
    exact hn ⟨x, hx, hk⟩
  obtain ⟨i, hi⟩ := (mem_treeGroup x).mp (hle hxE).1
  have hi_even : i ∈ evenInvolutionIndices := by
    apply even_involution_indices i
    · rw [hi]; exact Perm.mem_alternatingGroup.mp (hle hxE).2
    · rw [hi]; exact elemPow_eq_one_of_isElementaryAbelian x hxE
  have hi_out : i ∈ outsideIndices := by
    by_contra hn
    apply hxK
    change ∃ a b, x = kleinPerm a b
    simpa only [hi] using remaining_indices_klein i hi_even hn
  let index : E → Fin 128 := fun y =>
    Classical.choose ((mem_treeGroup (y : S)).mp (hle y.property).1)
  have hindex (y : E) : treeWord (index y) = (y : S) :=
    Classical.choose_spec ((mem_treeGroup (y : S)).mp (hle y.property).1)
  have hmem (y : E) : index y ∈ commutingIndices i := by
    apply Finset.mem_filter.mpr
    constructor
    · apply even_involution_indices
      · rw [hindex]; exact Perm.mem_alternatingGroup.mp (hle y.property).2
      · rw [hindex]; exact elemPow_eq_one_of_isElementaryAbelian _ y.property
    · rw [hindex, hi]
      exact congrArg Subtype.val (mul_comm y (⟨x, hxE⟩ : E))
  let f : E → {j // j ∈ commutingIndices i} := fun y => ⟨index y, hmem y⟩
  have hf : Function.Injective f := by
    intro y z h
    apply Subtype.ext
    rw [← hindex y, ← hindex z]
    exact congrArg treeWord (congrArg Subtype.val h)
  have hb := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe,
    commuting_indices_card i hi_out] using hb

/-- Every elementary subgroup of the even tree Sylow has order at most sixteen. -/
theorem permutation_even_tree_card_le (E : Subgroup S) [IsElementaryAbelian 2 E]
    (hle : E ≤ treeGroup ⊓ alternatingGroup (Fin 8)) : Nat.card E ≤ 16 := by
  by_cases h : E ≤ permutationA0
  · exact (Subgroup.card_le_of_le h).trans_eq (permutationActor_card 0)
  · exact (permutation_even_tree_card_le_twelve E hle h).trans (by decide)

/-- A₀ is the unique elementary subgroup of order at least sixteen in the even tree Sylow. -/
theorem permutation_even_tree_eq_A0_of_card_ge (E : Subgroup S)
    [IsElementaryAbelian 2 E] (hle : E ≤ treeGroup ⊓ alternatingGroup (Fin 8))
    (hcard : 16 ≤ Nat.card E) : E = permutationA0 := by
  have h : E ≤ permutationA0 := by
    by_contra hn
    have := permutation_even_tree_card_le_twelve E hle hn
    omega
  exact Subgroup.eq_of_le_of_card_ge h ((permutationActor_card 0).le.trans hcard)

/-- The two-block Klein subgroup lies in the actual binary-tree Sylow. -/
theorem permutationA0_le_treeGroup : permutationA0 ≤ treeGroup := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact treeGroup.mul_mem (treeGenerator_mem 0) (treeGenerator_mem 1)
  · exact treeGenerator_mem 4
  · exact treeGroup.mul_mem (treeGenerator_mem 2) (treeGenerator_mem 3)
  · exact treeGenerator_mem 5

/-- A specified Sylow subgroup in the actual automorphism group. -/
@[expose] noncomputable def T0 : Sylow 2 M :=
  treeSylow.comapOfInjective permutationEquiv.toMonoidHom permutationEquiv.injective
    (by rw [MonoidHom.range_eq_top.mpr permutationEquiv.surjective]; exact le_top)

@[simp] theorem T0_coe : (T0 : Subgroup M) =
    treeGroup.comap permutationEquiv.toMonoidHom := rfl

/-- The Sylow intersection is precisely the even part of the tree group in the marked action. -/
theorem T0_inner_map :
    ((T0 : Subgroup M) ⊓ inner).map permutationEquiv.toMonoidHom =
      treeGroup ⊓ alternatingGroup (Fin 8) := by
  have hi : inner = (alternatingGroup (Fin 8)).comap permutationEquiv.toMonoidHom := by
    ext a
    exact (permutationEquiv_mem_alternating a).symm
  rw [T0_coe, hi, ← Subgroup.comap_inf,
    Subgroup.map_comap_eq_self_of_surjective permutationEquiv.surjective]

/-- The marked elementary sixteen-subgroup is contained in the chosen Sylow intersection. -/
theorem A0_le_T0_inner : A0 ≤ (T0 : Subgroup M) ⊓ inner := by
  intro a ha
  exact ⟨permutationA0_le_treeGroup ha, A0_le_inner ha⟩

/-- The elementary order bound in the actual automorphism group. -/
theorem T0_inner_elementary_card_le (E : Subgroup M) [IsElementaryAbelian 2 E]
    (hle : E ≤ (T0 : Subgroup M) ⊓ inner) : Nat.card E ≤ 16 := by
  let : IsElementaryAbelian 2 (E.map permutationEquiv.toMonoidHom) :=
    IsElementaryAbelian.map permutationEquiv.toMonoidHom
  have h := permutation_even_tree_card_le (E.map permutationEquiv.toMonoidHom)
    (T0_inner_map ▸ Subgroup.map_mono hle)
  rwa [Subgroup.card_map_of_injective permutationEquiv.injective] at h

/-- No additional elementary subgroup can attain A₀'s order in this Sylow intersection. -/
theorem T0_inner_elementary_eq_A0_of_card_ge (E : Subgroup M)
    [IsElementaryAbelian 2 E] (hle : E ≤ (T0 : Subgroup M) ⊓ inner)
    (hcard : 16 ≤ Nat.card E) : E = A0 := by
  let : IsElementaryAbelian 2 (E.map permutationEquiv.toMonoidHom) :=
    IsElementaryAbelian.map permutationEquiv.toMonoidHom
  apply Subgroup.map_injective (f := permutationEquiv.toMonoidHom) permutationEquiv.injective
  rw [show A0 = actor 0 from rfl, actor_map]
  apply permutation_even_tree_eq_A0_of_card_ge _ (T0_inner_map ▸ Subgroup.map_mono hle)
  rwa [Subgroup.card_map_of_injective permutationEquiv.injective]

/-- Sylow conjugacy with an actual automorphism conjugator, respecting the inner intersection. -/
theorem exists_conj_sylow_inner_eq_T0 (T : Sylow 2 M) : ∃ a : M,
    (T : Subgroup M).map (MulAut.conj a).toMonoidHom = (T0 : Subgroup M) ∧
    ((T : Subgroup M) ⊓ inner).map (MulAut.conj a).toMonoidHom =
      (T0 : Subgroup M) ⊓ inner := by
  have : Finite M := Finite.of_equiv S permutationEquiv.symm.toEquiv
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq M T T0
  have hT : (T : Subgroup M).map (MulAut.conj a).toMonoidHom = (T0 : Subgroup M) :=
    congrArg Sylow.toSubgroup ha
  refine ⟨a, hT, ?_⟩
  have hi : (inner : Subgroup M).map (MulAut.conj a).toMonoidHom = (inner : Subgroup M) :=
    Subgroup.Normal.map_conj_eq inner a
  rw [Subgroup.map_inf _ _ _ (MulAut.conj a).injective, hT, hi]

end BinaryNaturalDual.FourActors.PermutationCatalogue
