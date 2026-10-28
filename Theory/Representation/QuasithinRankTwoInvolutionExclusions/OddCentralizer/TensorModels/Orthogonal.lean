module

public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Imprimitive.OrthogonalA5
public import Theory.Representation.BinaryPermutation.FiveGeometry
public import Theory.SpecificGroups.SymmetricFiveInvolutions
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.Tactic

/-!
# The orthogonal A₅ module and its S₅ extension

The even-weight core on five letters carries the invariant minus quadratic
form. Its actual S₅ action extends the A₅ action and is equivariantly identified
with the natural deleted permutation module. Transpositions have displacement
rank one; nonidentity even involutions have rank two. Hence the rank-one
involutions are exactly the transpositions. Only the small transposition-image
calculation is checked by finite reduction; form invariance uses singular
weights and permutation invariance of cardinality.

Source: Aschbacher–Smith, §B.3, G.11.2(9), printed p.364 (PDF p.375), and
the case-(9) argument in 6.2.19, printed p.691 (PDF p.708).
-/

@[expose] public section

namespace Representation.RankTwo.TensorModels.Orthogonal
abbrev S5 := Equiv.Perm (Fin 5)
abbrev Space := BinaryPermutation.core (Fin 5)
/-- The full five-point action extends the orthogonal A₅ module. -/
abbrev representation := BinaryPermutation.coreRepresentation (Fin 5)
lemma finrank_space : Module.finrank (ZMod 2) Space = 4 := by
  simpa using BinaryPermutation.finrank_core (Fin 5)

private def imageSet (p : S5) : Finset (Fin 5 → ZMod 2) :=
  (Finset.univ.filter (fun v : Fin 5 → ZMod 2 => ∑ i, v i = 0)).image
    (fun v i => v (p.symm i) - v i)
private lemma card_image_swap : ∀ i j : Fin 5, i ≠ j →
    (imageSet (Equiv.swap i j)).card = 2 := by decide +kernel

private noncomputable def coreImageEquiv (p : S5) :
    LinearMap.range (representation p - 1) ≃ ↥(imageSet p) := by
  let f : LinearMap.range (representation p - 1) → ↥(imageSet p) := fun z => ⟨z.val.val, by
    obtain ⟨v, hv⟩ := z.property
    apply Finset.mem_image.mpr
    refine ⟨v.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, v.property⟩, ?_⟩
    exact congrArg Subtype.val hv⟩
  apply Equiv.ofBijective f
  constructor
  · intro z w h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun u : ↥(imageSet p) => u.val) h
  · rintro ⟨w, hw⟩
    obtain ⟨v, hv, hvw⟩ := Finset.mem_image.mp hw
    let z : Space := ⟨v, (Finset.mem_filter.mp hv).2⟩
    refine ⟨⟨(representation p - 1) z, ⟨z, rfl⟩⟩, ?_⟩
    exact Subtype.ext hvw

lemma finrank_swap (p : S5) (hp : p.IsSwap) :
    Module.finrank (ZMod 2) (LinearMap.range (representation p - 1)) = 1 := by
  obtain ⟨i, j, hij, rfl⟩ := hp
  have hc : Nat.card (LinearMap.range (representation (Equiv.swap i j) - 1)) = 2 := by
    rw [Nat.card_congr (coreImageEquiv _), Nat.card_eq_fintype_card, Fintype.card_coe]
    exact card_image_swap i j hij
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
  exact Nat.pow_right_injective (by decide : 1 < 2) (hc.trans (pow_one 2).symm)

lemma finrank_even_involution (p : S5) (he : p ∈ alternatingGroup (Fin 5))
    (hp : p * p = 1) (hne : p ≠ 1) :
    Module.finrank (ZMod 2) (LinearMap.range (representation p - 1)) = 2 := by
  exact Imprimitive.OrthogonalA5.finrank_displacement ⟨p, he⟩
    (Subtype.ext hp) (fun h => hne (congrArg Subtype.val h))

lemma rank_one_iff_swap (p : S5) (hp : p * p = 1) :
    Module.finrank (ZMod 2) (LinearMap.range (representation p - 1)) = 1 ↔ p.IsSwap := by
  constructor
  · intro hr
    have hne : p ≠ 1 := by
      rintro rfl
      have hz : representation (1 : S5) = 1 := map_one representation
      rw [hz, sub_self, LinearMap.range_zero] at hr
      simp at hr
    by_cases he : p ∈ alternatingGroup (Fin 5)
    · rw [finrank_even_involution p he hp hne] at hr
      contradiction
    · apply Equiv.Perm.five_isSwap_of_outer_involution p _ he
      apply orderOf_eq_prime
      · simpa only [pow_two] using hp
      · exact hne
  · exact finrank_swap p

/-- The polynomial defining the minus four-space is preserved by the full extension. -/
lemma preserves_form (p : S5) (x : Space) :
    BinaryPermutation.FiveGeometry.form (representation p x) =
      BinaryPermutation.FiveGeometry.form x := by
  have hc : (Finset.univ.filter (fun i => (representation p x).val i ≠ 0)).card =
      (Finset.univ.filter (fun i => x.val i ≠ 0)).card := by
    simp only [Finset.card_filter]
    exact Equiv.sum_comp p.symm (fun i => if x.val i ≠ 0 then 1 else 0)
  have hz : representation p x = 0 ↔ x = 0 :=
    (representation.apply_bijective p).injective.eq_iff' (map_zero _)
  have he : BinaryPermutation.FiveGeometry.form (representation p x) = 0 ↔
      BinaryPermutation.FiveGeometry.form x = 0 := by
    rw [BinaryPermutation.FiveGeometry.singular_iff, BinaryPermutation.FiveGeometry.singular_iff,
      hz, hc]
  exact (by decide : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b) _ _ he

/-- The action restricted to A₅ is literally the already constructed orthogonal model. -/
lemma restriction (p : alternatingGroup (Fin 5)) (x : Space) :
    representation p.val x = Imprimitive.OrthogonalA5.representation p x := rfl
/-- The five-point core and the natural deleted permutation module are genuinely equivalent. -/
noncomputable def naturalEquiv :
    Representation.Equiv representation (BinaryPermutation.naturalRepresentation (Fin 5)) where
  toLinearEquiv := BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
  isIntertwining' p := by
    apply LinearMap.ext
    intro x
    exact BinaryPermutation.coreEquivNatural_equivariant (Fin 5) (by decide) p x

end Representation.RankTwo.TensorModels.Orthogonal
