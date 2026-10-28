module

public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.SourceData
public import CFSG.Quasithin.Defs

/-!
# Relative normalizers and choices of local factors

Aschbacher–Smith, *The Classification of Quasithin Groups*, combined manuscript
(1 March 2004), the notation preceding 15.4.19 and its assertion (2), printed
p.1163. Both normalizers in `T₀` are taken inside `T`. Equality of the two
factor stabilizers makes this intersection independent of either factor choice;
the relative-index intersection inequality gives its index at most four.

The outside-factor argument uses generation of `XT` by a factor and `T` and
uniqueness of the maximal two-local overgroup. A nontrivial normal two-module
in a factor also makes its two-core normalizer a two-local, so quasithinness
gives the three-rank bound required by `Source.LocalData`.

These lemmas apply to raw `Source.Geometry`; none assumes `Source.LocalData`
or a post-identification group model. The source assembly must construct their
stabilizer, generation and module hypotheses from 15.4.12.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup
open Subgroup
variable {G : Type*} [Group G]

/-- The intersection uses relative normalizers in the common Sylow subgroup. -/
theorem T₀_eq_intersection (d : Source.Geometry G) :
    d.T₀ = ((d.T : Subgroup G) ⊓ normalizer (d.X false : Set G)) ⊓
      ((d.T : Subgroup G) ⊓ normalizer (d.Y false : Set G)) := by
  symm
  rw [inf_inf_inf_comm, inf_idem, ← inf_assoc]
  rfl

/-- Exchanging either factor preserves the source subgroup `T₀`. -/
theorem T₀_eq_for_choices (d : Source.Geometry G)
    (hX : ∀ i, (d.T : Subgroup G) ⊓ normalizer (d.X i : Set G) =
      (d.T : Subgroup G) ⊓ normalizer (d.X false : Set G))
    (hY : ∀ j, (d.T : Subgroup G) ⊓ normalizer (d.Y j : Set G) =
      (d.T : Subgroup G) ⊓ normalizer (d.Y false : Set G)) (i j : Bool) :
    d.T₀ = ((d.T : Subgroup G) ⊓ normalizer (d.X i : Set G)) ⊓
      ((d.T : Subgroup G) ⊓ normalizer (d.Y j : Set G)) := by
  rw [hX i, hY j]
  exact T₀_eq_intersection d

/-- The index bound before 15.4.19 follows from the two stabilizers of index two. -/
theorem T₀_relIndex_le_four (d : Source.Geometry G)
    (hX : ((d.T : Subgroup G) ⊓ normalizer (d.X false : Set G)).relIndex
      (d.T : Subgroup G) = 2)
    (hY : ((d.T : Subgroup G) ⊓ normalizer (d.Y false : Set G)).relIndex
      (d.T : Subgroup G) = 2) : d.T₀.relIndex (d.T : Subgroup G) ≤ 4 := by
  rw [T₀_eq_intersection]
  have hi := relIndex_inf_le (H := (d.T : Subgroup G) ⊓ normalizer (d.X false : Set G))
    (K := (d.T : Subgroup G) ⊓ normalizer (d.Y false : Set G)) (L := (d.T : Subgroup G))
  simpa only [hX, hY] using hi

/-- The uniqueness argument in 15.4.19(2) uses generation by a single factor
and `T`, before any identification of that factor. -/
theorem factor_not_le_other {L X T M₁ M₂ : Subgroup G}
    (hgen : L ⊔ T = X ⊔ T)
    (hunique : ∀ M : Subgroup G, IsMaximalTwoLocal M → X ⊔ T ≤ M → M = M₁)
    (hM₂ : IsMaximalTwoLocal M₂) (hTM₂ : T ≤ M₂) (hne : M₁ ≠ M₂) : ¬ L ≤ M₂ := by
  intro hLM₂
  have hXM₂ : X ⊔ T ≤ M₂ := hgen ▸ sup_le hLM₂ hTM₂
  exact hne (hunique M₂ hM₂ hXM₂).symm

/-- The normalizer rank bound in `Source.LocalData` follows directly from QT,
once a nontrivial normal two-module in the factor is known. -/
theorem normalizer_three_rank_le_two [Finite G] (hG : IsQuasithin G)
    {L V : Subgroup G} (hV : IsPGroup 2 V) (hne : V ≠ ⊥)
    (hVL : V ≤ L) (hLN : L ≤ normalizer (V : Set G)) :
    primeRank 3 (normalizer (L.pCoreIn 2 : Set G)) ≤ 2 := by
  have hcore : L.pCoreIn 2 ≠ ⊥ := by
    intro hbot
    exact hne (le_bot_iff.mp (hbot ▸ le_pCoreIn_of_normalizes hV hVL hLN))
  exact isQuasithin_iff_twoLocal.mp hG _
    ⟨L.pCoreIn 2, hcore, isPGroup_pCoreIn 2 L, rfl⟩ 3 (by decide) (by decide)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup
