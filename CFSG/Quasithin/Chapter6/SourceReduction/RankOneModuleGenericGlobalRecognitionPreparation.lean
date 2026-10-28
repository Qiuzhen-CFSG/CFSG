module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobal
public import CFSG.Quasithin.ChapterF.Section01.SourceLocalResidual
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents

/-!
# Parabolic residuals before generic amalgam recognition

The complete local selection provides a perfect right factor. The original
left factor is perfect by its local-family membership. Since both parabolics
have solvable quotient by their selected factor, their solvable residuals
are exactly those factors. Escape of the right factor proves it nontrivial,
so neither parabolic is solvable. The full right Borel normalizes the
original S = O₂(N_G(L) ∩ H), by its proved Hall product.

These supply the first deductions in 5.2.6 and the extra Borel normalization
required by F.1.12. They do not classify the amalgam, identify the right
factor with O²(H), or recognize its ambient completion. Those obligations
remain with qt-d-1222-rankone-generic-global; the Chapter 12 extension
applies every result to the actually constructed pair.

Source: Aschbacher–Smith, 5.2.4–6, printed pp.649–651,
and F.1.12, pp.262–264 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The right Borel acts on S, as required for the F.1.12 application. -/
theorem Preparation.right_borel_normalizes_sourceS
    {T : Sylow 2 G} {L H A B R : Subgroup G} (d : Preparation T L H A B R) :
    ChapterF.Source.borel R (sourceS L H) ≤ normalizer (sourceS L H : Set G) := by
  rw [d.right_borel]
  exact sup_le (inf_le_left.trans (sourceS L H).le_normalizer)
    (inf_le_left.trans (d.cartans.right_le.trans (intersection_normalizes_sourceS L H)))

/-- Perfect selected factors are precisely the original parabolic residuals. -/
theorem Preparation.parabolic_residuals
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B R)
    (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hR : Group.IsPerfect R) :
    ∀ i : Fin 2, (solvableResidual (ChapterF.Source.parabolic ![L,R] (sourceS L H) i)).map
      (ChapterF.Source.parabolic ![L,R] (sourceS L H) i).subtype = ![L,R] i := by
  have hp : ∀ i : Fin 2, Group.IsPerfect (![L,R] i) := by
    intro i
    fin_cases i
    · exact Chapter1.mem_L_isPerfect h.local_mem.1.1
    · exact hR
  intro i
  let := hp i
  rw [←(d.hypothesisF11 h hTH).local_residual_eq_parabolic i,solvableResidual_eq_top,
    ←MonoidHom.range_eq_map,range_subtype]

/-- Neither original parabolic is solvable, so the solvable local rows of
F.1.12 cannot occur for this selected pair. -/
theorem Preparation.parabolics_not_solvable
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B R)
    (h : Input κ T L W n) (hR : Group.IsPerfect R) :
    ∀ i : Fin 2, ¬ Group.IsSolvable (ChapterF.Source.parabolic ![L,R] (sourceS L H) i) := by
  have hp : ∀ i : Fin 2, ¬ Group.IsSolvable (![L,R] i) := by
    intro i
    fin_cases i
    · exact Chapter1.mem_L_not_isSolvable h.local_mem.1.1
    · let := hR
      have hr : R ≠ ⊥ := fun he => d.right_outside (he ▸ bot_le)
      let : Nontrivial R := (nontrivial_iff_ne_bot R).mpr hr
      exact Group.IsPerfect.not_isSolvable R
  intro i hs
  let := hs
  exact hp i (Group.isSolvable_of_isSolvable_injective
    (f := inclusion (show ![L,R] i ≤ ChapterF.Source.parabolic ![L,R] (sourceS L H) i from
      le_sup_left.trans le_sup_left)) (inclusion_injective _))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
