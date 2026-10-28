module

public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks.LocalRank
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks.ElementaryTorus
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks.MinusEmbedding
import Mathlib.Tactic

/-!
# Higher orthogonal ranks are not quasithin over even fields larger than two

For every finite field of characteristic two with more than two elements,
`PΩ⁺₂ᵣ(F)` is not quasithin for `r ≥ 3`, and `PΩ⁻₂ᵣ(F)` is not quasithin
for `r ≥ 4`. The boundary cases `PΩ⁺₆` and `PΩ⁻₈` are included.

The displayed Siegel root survives the literal scalar quotient and is a
nontrivial two-group. Squared diagonal parameters on three hyperbolic pairs
normalize it and embed faithfully. A prime dividing `|F|-1` is odd, and its
roots of unity give an elementary group of order `p³` in the actual normalizer.
The plus diagonal membership is proved by elementary root words. The minus
root and torus membership are proved in the full isometry commutator group,
then extended by the identity on the actual chosen anisotropic plane.
Every extra membership premise of the shared local argument is discharged here.

This supplies the orthogonal model instances of the Cartan obstruction in
Aschbacher–Smith, *The Classification of Quasithin Groups*, A.2.18 (printed
p.40), used in Theorem D/14.8.2 (pp.1078–1079). Model and root conventions
are those of GLS3 §2.7 (`refs/KGroup/GLS3/chapter2.tex`). No order formula,
simplicity theorem, algebraic closure, or parabolic induction is assumed.
-/

set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
universe u
namespace ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks
variable {F : Type u} [Field F] {r : ℕ}

section Plus
variable [CharP F 2] {i j : Fin r} (hij : i ≠ j)

/-- A genuine root two-subgroup in the literal projective elementary plus model. -/
def plusRootSubgroup : Subgroup (POmegaPlus r F) :=
  liftedRootSubgroup (elementarySubgroup (formD r F)) (projectiveElementaryMap (formD r F))
    hij (root_mem_elementary hij)

abbrev plusRootNormalizer : Subgroup (POmegaPlus r F) :=
  Subgroup.normalizer (plusRootSubgroup (F := F) hij : Set (POmegaPlus r F))

theorem plusRootSubgroup_ne_bot : plusRootSubgroup (F := F) hij ≠ ⊥ :=
  liftedRootSubgroup_ne_bot _ _ hij _ (elementaryProjective_injective _)

theorem plusRootSubgroup_isTwoGroup : IsPGroup 2 (plusRootSubgroup (F := F) hij) :=
  liftedRootSubgroup_isTwoGroup _ _ hij _

/-- Three independent squared diagonal parameters in the literal plus root normalizer. -/
def plusTorusNormalizerHom (hr : 2 ≤ r) (C : Subgroup Fˣ) :
    (Fin 3 → C) →* (plusRootNormalizer (F := F) hij) :=
  torusNormalizerHom _ _ hij (root_mem_elementary hij) (diagonal_square_mem_elementary hr) C

theorem plusTorusNormalizerHom_injective (hr : 3 ≤ r) (C : Subgroup Fˣ) :
    Function.Injective (plusTorusNormalizerHom hij (by omega) C) :=
  torusNormalizerHom_injective _ _ hij _ _ hr (elementaryProjective_injective _) C

/-- Each prime dividing `|F|-1` gives rank three in this actual two-local subgroup. -/
theorem plus_primeRank_rootNormalizer_ge_three [Finite F] (hr : 3 ≤ r)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ Nat.card F - 1) :
    3 ≤ primeRank p (plusRootNormalizer (F := F) hij) :=
  primeRank_liftedRootNormalizer_ge_three _ _ hij _ (diagonal_square_mem_elementary (by omega))
    hr (elementaryProjective_injective _) hp hd

/-- The requested elementary odd-prime witness inside the plus root normalizer. -/
theorem plus_rootNormalizer_witness [Finite F] (hr : 3 ≤ r) (hq : 2 < Nat.card F) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ Nat.card F - 1 ∧
      ∃ f : (Fin 3 → rootsOfUnity p F) →* plusRootNormalizer (F := F) hij,
        Function.Injective f ∧ (∀ a : Fin 3 → rootsOfUnity p F, a ^ p = 1) ∧
          Nat.card (Fin 3 → rootsOfUnity p F) = p ^ 3 :=
  liftedRootNormalizer_witness _ _ hij _ (diagonal_square_mem_elementary (by omega))
    hr (elementaryProjective_injective _) hq

/-- Intrinsic exclusion of every plus rank at least three, including `PΩ₆⁺`. -/
theorem not_quasithin_plus [Finite F] (hr : 3 ≤ r) (hq : 2 < Nat.card F) :
    ¬ IsQuasithin (POmegaPlus r F) := by
  let i : Fin r := ⟨0, by omega⟩
  let j : Fin r := ⟨1, by omega⟩
  have hij : i ≠ j := Fin.ne_of_val_ne (by simp [i, j])
  exact not_quasithin_of_coordinates (elementarySubgroup (formD r F))
    (projectiveElementaryMap (formD r F)) hij (root_mem_elementary hij)
    (diagonal_square_mem_elementary (by omega)) hr (elementaryProjective_injective _) hq
end Plus

section Minus
variable [Finite F] [CharP F 2] (hq : 2 < Nat.card F)
variable {i j : Fin (r-1)} (hij : i ≠ j)

/-- A root two-subgroup in the exact projective commutator minus model. -/
def minusRootSubgroup : Subgroup (ClassicalGroup.POmegaMinus r F) :=
  liftedRootSubgroup (commutator (O (r-1) F)) (minusProjectiveHom r)
    hij (root_mem_commutator hq hij)

abbrev minusRootNormalizer : Subgroup (ClassicalGroup.POmegaMinus r F) :=
  Subgroup.normalizer (minusRootSubgroup hq hij : Set (ClassicalGroup.POmegaMinus r F))

theorem minusRootSubgroup_ne_bot : minusRootSubgroup hq hij ≠ ⊥ :=
  liftedRootSubgroup_ne_bot _ _ hij _ (minusProjectiveHom_injective r)

theorem minusRootSubgroup_isTwoGroup : IsPGroup 2 (minusRootSubgroup hq hij) :=
  liftedRootSubgroup_isTwoGroup _ _ hij _

/-- Three independent squared diagonal parameters after extension by the anisotropic plane. -/
def minusTorusNormalizerHom (C : Subgroup Fˣ) :
    (Fin 3 → C) →* (minusRootNormalizer hq hij) :=
  torusNormalizerHom _ _ hij (root_mem_commutator hq hij) diagonal_square_mem_commutator C

theorem minusTorusNormalizerHom_injective (hr : 4 ≤ r) (C : Subgroup Fˣ) :
    Function.Injective (minusTorusNormalizerHom hq hij C) :=
  torusNormalizerHom_injective _ _ hij _ _ (by omega) (minusProjectiveHom_injective r) C

theorem minus_primeRank_rootNormalizer_ge_three (hr : 4 ≤ r)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ Nat.card F - 1) :
    3 ≤ primeRank p (minusRootNormalizer hq hij) :=
  primeRank_liftedRootNormalizer_ge_three _ _ hij _ diagonal_square_mem_commutator
    (by omega) (minusProjectiveHom_injective r) hp hd

/-- The requested elementary odd-prime witness inside the minus root normalizer. -/
theorem minus_rootNormalizer_witness (hr : 4 ≤ r) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ Nat.card F - 1 ∧
      ∃ f : (Fin 3 → rootsOfUnity p F) →* minusRootNormalizer hq hij,
        Function.Injective f ∧ (∀ a : Fin 3 → rootsOfUnity p F, a ^ p = 1) ∧
          Nat.card (Fin 3 → rootsOfUnity p F) = p ^ 3 :=
  liftedRootNormalizer_witness _ _ hij _ diagonal_square_mem_commutator
    (by omega) (minusProjectiveHom_injective r) hq

include hq in
/-- Intrinsic exclusion of every minus rank at least four, including `PΩ₈⁻`. -/
theorem not_quasithin_minus (hr : 4 ≤ r) :
    ¬ IsQuasithin (ClassicalGroup.POmegaMinus r F) := by
  let i : Fin (r-1) := ⟨0, by omega⟩
  let j : Fin (r-1) := ⟨1, by omega⟩
  have hij : i ≠ j := Fin.ne_of_val_ne (by simp [i, j])
  exact not_quasithin_of_coordinates (commutator (O (r-1) F)) (minusProjectiveHom r)
    hij (root_mem_commutator hq hij) diagonal_square_mem_commutator
    (by omega) (minusProjectiveHom_injective r) hq
end Minus

end ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks
