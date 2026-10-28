module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.Sylow
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalReeCompletion.Centers

/-!
# The original Chapter12 Ree Sylow and centralizer residuals

The actual Suzuki quotient and enlarged-core identity force the common
parabolic Sylow to be the whole ambient Sylow, with H = O²(H). Both full
normalizers have their original perfect factors as solvable residuals.
The solvable residual of every long-root involution centralizer has order
prime to three. These are unconditional consequences of the original
prepared comparison, with both orientations and the whole overlap retained.

The compatible native extension, short-root centralizer and ambient order
comparison remain before native recognition and GlobalExit.
Source: Aschbacher–Smith 5.3.1–3, F.4.35,38 and 12.2.2,
printed pp.658–659,292,294,795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original Sylow equals the common parabolic Sylow and lies in both factors. -/
theorem rankOne_global_ree_full_sylow
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m).reverse)) :
    Global.sourceS L H = (T : Subgroup G) ∧
      (T : Subgroup G) ≤ L ∧ (T : Subgroup G) ≤ residual H ∧ residual H = H := by
  exact d.ree_full_sylow (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m he

/-- Exact solvable residuals of the full normalizers and the three-free
long-root centralizer residual, without any additional local-action premise. -/
theorem rankOne_global_ree_normalizer_residuals
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m).reverse)) :
    (∀ i : Fin 2, (solvableResidual (normalizer (![L,residual H] i : Set G))).map
      (normalizer (![L,residual H] i : Set G)).subtype = ![L,residual H] i) ∧
    ∀ z ∈ (center (residual H)).map (residual H).subtype, orderOf z = 2 →
      ¬ 3 ∣ Nat.card (solvableResidual (centralizer ({z} : Set G))) := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨d.ree_normalizer_residuals hi hH hp m he,
    d.ree_long_centralizer_residual_three_free hi hH hp m he⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
