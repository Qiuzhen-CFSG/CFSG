module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.SplitNormalForm.CellSeparation.Height

/-!
# Upper matrices and the split normalizer intersection

Upper matrices have no off-diagonal entries of nonpositive height difference.
The positive subgroup consists of such matrices. Once the actual torus is
shown upper, the Borel is upper as well. If a Weyl matrix has a nonzero entry
at every permuted root position, upperness forces its permutation to be the
identity: a permutation cannot strictly increase any heights without decreasing
others. This yields B ∩ N = H from the published normalizer factorization.

The torus and Weyl entry premises below are explicit matrix obligations,
not asserted consequences of the abstract Inputs record.
Source: GLS3 2.3.4(b), `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section
namespace Triality.Standard.ConcreteBruhat.SplitNormalForm.CellSeparation
noncomputable section
open Parabolics PositiveCoordinates.Injectivity Parabolics.RankOneMatrices
open Theory.AlgebraicGroup.StandardRootSystem
open scoped BigOperators Pointwise
attribute [local instance] matrixLatticeDecidableEq

/-- Off-diagonal entries vanish unless they strictly raise degree. -/
def Upper {F : Type*} [Zero F] (A : Matrix LatticeIndex LatticeIndex F) : Prop :=
  ∀ i j, i ≠ j → degree i ≤ degree j → A i j = 0

lemma upper_mul {F : Type*} [CommRing F]
    {A B : Matrix LatticeIndex LatticeIndex F} (ha : Upper A) (hb : Upper B) :
    Upper (A * B) := by
  intro i j hij hd
  apply Finset.sum_eq_zero
  intro k _
  change A i k * B k j = 0
  by_cases hik : i = k
  · subst k
    rw [hb i j hij hd, mul_zero]
  · by_cases hkj : k = j
    · subst k
      rw [ha i j hij hd, zero_mul]
    · by_cases hdik : degree i ≤ degree k
      · rw [ha i k hik hdik, zero_mul]
      · rw [hb k j hkj (by linarith), mul_zero]

lemma upper_of_raises {F : Type*} [CommRing F]
    {A : Matrix LatticeIndex LatticeIndex F} (ha : Raises degree 1 (A - 1)) :
    Upper A := by
  intro i j hij hd
  have h := ha i j (by linarith)
  simpa [Matrix.sub_apply, Matrix.one_apply, hij] using h

lemma upper_borel (n : ℕ) (hn : 0 < n) (D : Inputs (binaryParameters n hn))
    (ht : ∀ t : splitTorus (binaryParameters n hn), Upper (matrix _ t.val))
    {g : SplitGroup (binaryParameters n hn)} (hg : g ∈ splitBorel _) :
    Upper (matrix _ g) := by
  obtain ⟨⟨u, t⟩, he, _⟩ := D.existsUnique_borel_factors ⟨g, hg⟩
  dsimp only at he
  rw [← he, map_mul]
  exact upper_mul (upper_of_raises (positive_raises n hn u.property)) (ht t)

lemma matrix_injective (P : Parameters) : Function.Injective (matrix P) := by
  intro a b h
  exact Subtype.ext (Units.ext h)

lemma eq_one_of_upper_of_lowers (P : Parameters) {g : SplitGroup P}
    (hu : Upper (matrix P g))
    (hl : Raises (fun i => -degree i) 1 (matrix P g - 1)) : g = 1 := by
  apply matrix_injective P
  rw [map_one]
  ext i j
  by_cases hij : i = j
  · subst j
    exact sub_eq_zero.mp (hl i i (by linarith))
  · by_cases hd : degree i ≤ degree j
    · rw [hu i j hij hd, Matrix.one_apply_ne hij]
    · exact sub_eq_zero.mp (hl i j (by linarith))

/-- A root permutation carried by an upper matrix must fix every root. -/
lemma weyl_eq_one_of_upper {P : Parameters} (D : Inputs P) (w : rootWeylGroup)
    (hu : Upper (matrix P (D.lift w)))
    (hpivot : ∀ r : TypeDRootIndex 4,
      matrix P (D.lift w) (.inr (w.val r)) (.inr r) ≠ 0) : w = 1 := by
  have hstrict (r : TypeDRootIndex 4) (hr : w.val r ≠ r) :
      degree (.inr r) < degree (.inr (w.val r)) := by
    by_contra h
    exact hpivot r (hu _ _ (fun he => hr (Sum.inr.inj he)) (by linarith))
  have hle (r : TypeDRootIndex 4) : degree (.inr r) ≤ degree (.inr (w.val r)) := by
    by_cases hr : w.val r = r
    · rw [hr]
    · exact (hstrict r hr).le
  have heq : ∀ r, degree (.inr r) = degree (.inr (w.val r)) := by
    have hs : (∑ r : TypeDRootIndex 4, degree (.inr r)) =
        ∑ r : TypeDRootIndex 4, degree (.inr (w.val r)) :=
      (Equiv.sum_comp w.val (fun r => degree (.inr r))).symm
    exact fun r => (Finset.sum_eq_sum_iff_of_le (fun s _ => hle s)).mp hs r (Finset.mem_univ r)
  apply Subtype.ext
  apply Equiv.ext
  intro r
  by_contra hr
  exact (hstrict r hr).ne (heq r)

/-- Normalizer intersection, conditional only on torus support and Weyl matrix entries. -/
lemma borel_inf_normalizer_of_matrix_entries (n : ℕ) (hn : 0 < n)
    (D : Inputs (binaryParameters n hn))
    (ht : ∀ t : splitTorus (binaryParameters n hn), Upper (matrix _ t.val))
    (hpivot : ∀ (w : rootWeylGroup) (r : TypeDRootIndex 4),
      matrix _ (D.lift w) (.inr (w.val r)) (.inr r) ≠ 0) :
    splitBorel (binaryParameters n hn) ⊓ splitNormalizer _ = splitTorus _ := by
  apply le_antisymm
  · intro g hg
    have hset := Subgroup.coe_mul_of_right_le_normalizer_left
      (splitTorus (binaryParameters n hn)) (splitWeylSubgroup (binaryParameters n hn))
      D.weyl_normalizes_torus
    have hmem : g ∈ (splitNormalizer (binaryParameters n hn) :
        Set (SplitGroup (binaryParameters n hn))) := hg.2
    rw [splitNormalizer] at hmem
    rw [hset] at hmem
    obtain ⟨t, htmem, v, hv, rfl⟩ := hmem
    have hvb : v ∈ splitBorel _ := by
      have h := (splitBorel _).mul_mem
        ((splitBorel _).inv_mem (splitTorus_le_splitBorel _ htmem)) hg.1
      simpa only [inv_mul_cancel_left] using h
    let w := D.weylEquiv ⟨v, hv⟩
    have hw : D.lift w = v := by
      change (D.weylEquiv.symm (D.weylEquiv ⟨v, hv⟩)).val = v
      rw [D.weylEquiv.symm_apply_apply]
    have hw1 := weyl_eq_one_of_upper D w
      (hw.symm ▸ upper_borel n hn D ht hvb) (hpivot w)
    have hv1 : v = 1 := by rw [← hw, hw1, map_one]
    change t * v ∈ splitTorus (binaryParameters n hn)
    rw [hv1, mul_one]
    exact htmem
  · exact le_inf (splitTorus_le_splitBorel _) le_sup_left


end
end Triality.Standard.ConcreteBruhat.SplitNormalForm.CellSeparation
