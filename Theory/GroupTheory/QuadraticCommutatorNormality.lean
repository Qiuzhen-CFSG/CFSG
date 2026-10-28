module

public import Theory.GroupTheory.Commutator.NormalClosure

/-!
# Normality of a quadratic commutator under a generating family

If `A` acts quadratically on the normal closure of `V`, then `A` centralizes
`[V,A ∩ Q]`. A subgroup centralizing `V` also centralizes this commutator
when `A ∩ Q` normalizes `V`. Thus normalization by the third member of a
generating family implies normality in the whole group.

The source application is the generation argument in Aschbacher--Smith,
combined manuscript (1 March 2004), Lemma 15.2.11, printed p.1111.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

/-- The source generation argument proves normality for `B = A ∩ Q`. -/
theorem commutator_normal_of_quadratic_generation (V Q X A T : Subgroup G)
    (hBV : A ⊓ Q ≤ normalizer (V : Set G))
    (hquadratic : ⁅⁅normalClosure (V : Set G), A⁆, A⁆ = ⊥)
    (hXV : X ≤ centralizer (V : Set G))
    (hTZ : T ≤ normalizer (⁅V, A ⊓ Q⁆ : Subgroup G))
    (hgen : (X ⊔ A) ⊔ T = ⊤) : (⁅V, A ⊓ Q⁆).Normal := by
  have hZV : ⁅V, A ⊓ Q⁆ ≤ V :=
    le_normalizer_iff_commutator_le_left.mp hBV
  have hZA : ⁅⁅V, A ⊓ Q⁆, A⁆ = ⊥ := by
    apply bot_unique
    exact (commutator_mono (commutator_mono le_normalClosure inf_le_left) le_rfl).trans
      hquadratic.le
  have hXZ : X ≤ centralizer (⁅V, A ⊓ Q⁆ : Subgroup G) :=
    hXV.trans (centralizer_le hZV)
  have hAZ : A ≤ centralizer (⁅V, A ⊓ Q⁆ : Subgroup G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hZA)
  apply normalizer_eq_top_iff.mp
  apply top_le_iff.mp
  rw [← hgen]
  exact sup_le (sup_le (hXZ.trans (centralizer_le_normalizer _))
    (hAZ.trans (centralizer_le_normalizer _))) hTZ

end Subgroup
