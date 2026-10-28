module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.SupportGeneration

/-!
# Reindexing the actual five-factors

Permuting the factors preserves their literal subgroup inclusions, moved
supports and all factorization properties. A chosen moved factor can therefore
be placed first without choosing an unrelated decomposition. Generation also
passes through the actual quotient map to H/O₂(H).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.13,
printed p.951, the choice of the first moved five-factor.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
variable {G : Type*} [Group G]
variable {H UH V₁ : Subgroup G} [(V₁.subgroupOf UH).Normal]
variable {a : StarAction H UH V₁} {P : Subgroup G}

noncomputable def Factorization.reindex (f : Factorization a P) (e : Equiv.Perm (Fin f.count)) :
    Factorization a P where
  count := f.count
  count_pos := f.count_pos
  count_le_two := f.count_le_two
  factor i := f.factor (e i)
  factor_le i := f.factor_le (e i)
  factor_card i := f.factor_card (e i)
  star_card i := f.star_card (e i)
  generated := f.generated.trans (e.surjective.iSup_comp f.factor).symm
  commute i j h := f.commute (e i) (e j) (e.injective.ne h)
  disjoint i j h := f.disjoint (e i) (e j) (e.injective.ne h)
  support_card i := f.support_card (e i)
  support_disjoint i j h := f.support_disjoint (e i) (e j) (e.injective.ne h)

theorem Factorization.reindex_factor (f : Factorization a P)
    (e : Equiv.Perm (Fin f.count)) (i : Fin f.count) :
    (f.reindex e).factor i = f.factor (e i) := rfl

theorem Factorization.reindex_support (f : Factorization a P)
    (e : Equiv.Perm (Fin f.count)) (i : Fin f.count) :
    (f.reindex e).support i = f.support (e i) := rfl

theorem Factorization.star_generated (f : Factorization a P) (hPH : P ≤ H) :
    Source.starImage H P = ⨆ i, Source.starImage H (f.factor i) := by
  have hi : P.subgroupOf H = ⨆ i, (f.factor i).subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hPH, Subgroup.map_iSup]
    simp_rw [map_subgroupOf_eq_of_le ((f.factor_le _).trans hPH)]
    exact f.generated
  simp only [Source.starImage, hi, Subgroup.map_iSup]

theorem Factorization.reindex_first (f : Factorization a P) (i : Fin f.count) :
    ∃ f' : Factorization a P, f'.count = f.count ∧
      f'.factor ⟨0, f'.count_pos⟩ = f.factor i ∧
      ∃ e : Fin f'.count ≃ Fin f.count, ∀ j, f'.factor j = f.factor (e j) := by
  classical
  let e := Equiv.swap (⟨0, f.count_pos⟩ : Fin f.count) i
  refine ⟨f.reindex e, rfl, ?_, e, fun _ => rfl⟩
  change f.factor (e ⟨0, f.count_pos⟩) = f.factor i
  rw [Equiv.swap_apply_left]

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
end
