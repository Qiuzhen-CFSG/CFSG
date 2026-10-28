module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Odd
public import Theory.SpecificGroups.SymmetricSeven.ThreePairsFixed

/-!
# The natural fixed-space fixer for three disjoint swaps

The three pair vectors distinguish the three two-point orbits and the final
fixed letter. Any permutation fixing these vectors can only interchange
letters within a pair, so belongs to the elementary eight. This identifies
the two existing markings used in B.3.2 and the cubic construction.

Source: Aschbacher–Smith C.1.24, printed p.131.
-/

@[expose] public section
open Subgroup Equiv BinaryPermutation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.RankOne.Alternating.SevenSource
open ChapterB.Offenders
open Representation.AlternatingSevenConjugatePair.ElementaryGeometry

/-- The offender and explicit permutation-word markings agree literally. -/
theorem natural_D_eq_pairElementary : D 7 = pairElementary := by
  apply eq_of_le_of_card_ge
  · rw [D, disjointTranspositions, closure_le]
    rintro g ⟨i, hi, rfl⟩
    exact (by decide +kernel : ∀ i : Fin 3, pairSwap 7 i ∈ pairElementary) i
  · rw [pairElementary_card, D,
      Odd.card_disjointTranspositions (Or.inr rfl) (le_refl (7 / 2))]
    decide

/-- Fixing the natural fixed space permits only the three pair swaps. -/
theorem natural_fixed_space_fixer_le_D (g : Perm (Fin 7))
    (hf : ∀ v ∈ fixedSpace (coreRepresentation (Fin 7)) (D 7),
      coreRepresentation (Fin 7) g v = v) : g ∈ D 7 := by
  rw [natural_D_eq_pairElementary] at hf ⊢
  exact (Theory.SpecificGroups.SymmetricSeven.ThreePairsFixed.mem_pairElementary_iff_fixes_fixedSpace g).mpr hf

/-- The same pointwise fixer in any conjugate source marking. -/
theorem natural_fixed_space_fixer_le_conjugate_D (a g : Perm (Fin 7))
    (hf : ∀ v ∈ fixedSpace (coreRepresentation (Fin 7))
      ((D 7).map (MulAut.conj a).toMonoidHom), coreRepresentation (Fin 7) g v = v) :
    g ∈ (D 7).map (MulAut.conj a).toMonoidHom := by
  let ρ := coreRepresentation (Fin 7)
  have hg : a⁻¹ * g * a ∈ D 7 := by
    apply natural_fixed_space_fixer_le_D
    intro v hv
    have hva : ρ a v ∈ fixedSpace ρ ((D 7).map (MulAut.conj a).toMonoidHom) := by
      rintro ⟨x, b, hb, rfl⟩
      change ρ (a * b * a⁻¹) (ρ a v) = ρ a v
      rw [map_mul, map_mul]
      simp only [Module.End.mul_apply]
      have hcancel : ρ a⁻¹ (ρ a v) = v := by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      have hvb : ρ b v = v := hv ⟨b, hb⟩
      rw [hcancel, hvb]
    have hw := hf (ρ a v) hva
    change ρ g (ρ a v) = ρ a v at hw
    have hh := congrArg (ρ a⁻¹) hw
    change ρ (a⁻¹ * g * a) v = v
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply, mul_assoc] using hh
  refine ⟨a⁻¹ * g * a, hg, ?_⟩
  simp [MulAut.conj_apply, mul_assoc]

end CFSG.Quasithin.ChapterC.RankOne.Alternating.SevenSource
