module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.BinaryBranch.SourceClassification.QuasisimpleApplication
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.SmallSylow
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder

/-!
# Incompatible quasisimple actors in the binary source module list

The actual source socle has order 20160 or 9999360. Its two-part is at
most 1024. The unipotent groups bound the field degrees in the SL₂,
Sp₄ and G₂ alternatives of B.4.2. The SL₂ order formula then excludes
every possible degree; Sp₄ over the only remaining larger field has a
factor 17; and a larger-field G₂ already has excessive two-part.

Only genuine group equivalences from the source module clauses are used.
Source: Aschbacher–Smith, B.4.2, p.86; 15.4.20, p.1164.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.BinaryBranch.SourceClassification.Recognition
open TwoFactors.FFBranch.ClassificationComparison FFAlternatives

/-- The orders are those of the literal generalized Fitting subgroup. -/
theorem sourceFitting_card {G : Type*} [Group G] [Finite G]
    {d : Source.Geometry G} {i j : Bool} {H U K : Subgroup G}
    (h : Input d i j H U K) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : (H ⧸ pCore 2 H) ≃* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) :
    Nat.card (generalizedFitting (sourceGroup h)) = 20160 ∨
      Nat.card (generalizedFitting (sourceGroup h)) = 9999360 := by
  rw [Nat.card_congr (sourceFittingEquivPSL h hn e).toEquiv]
  rcases hn with rfl | rfl
  · left
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 4
    norm_num only [Nat.card_zmod, Fin.prod_univ_succ, Fin.prod_univ_zero,
      Fin.val_zero, Fin.val_succ, Nat.mul_one] at hc
    exact hc
  · right
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 5
    norm_num only [Nat.card_zmod, Fin.prod_univ_succ, Fin.prod_univ_zero,
      Fin.val_zero, Fin.val_succ, Nat.mul_one] at hc
    exact hc

private theorem power_bound {c k : ℕ} (hc : c = 20160 ∨ c = 9999360)
    (hk : 2 ^ k ∣ c) : k ≤ 10 := by
  by_contra hn
  have hd : 2048 ∣ c := (pow_dvd_pow 2 (by omega : 11 ≤ k)).trans hk
  rcases hc with rfl | rfl <;> norm_num at hd

variable {L : Type*} [Group L]

/-- No binary rank-one group is isomorphic to the actual binary source socle. -/
theorem no_linearTwo (hc : Nat.card L = 20160 ∨ Nat.card L = 9999360)
    (F : BinaryField) (e : L ≃* SL(2,F.Carrier)) : False := by
  have he : Nat.card L = 2 ^ F.degree * ((2 ^ F.degree) ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, GorensteinWalter.sl2_card_formula, F.card_eq]
  have hb : F.degree ≤ 10 := power_bound hc (by rw [he]; exact dvd_mul_right _ _)
  have hp := F.degree_pos
  interval_cases hf : F.degree <;> rcases hc with hc | hc <;> norm_num [hf, hc] at he

/-- The larger-field symplectic row cannot be either binary source socle. -/
theorem no_symplectic (hc : Nat.card L = 20160 ∨ Nat.card L = 9999360)
    (F : BinaryField) (hF : 1 < F.degree)
    (e : L ≃* Matrix.symplecticGroup (Fin 2) F.Carrier) : False := by
  have hd := (Theory.SpecificGroups.SymplecticFour.unipotent (F := F.Carrier)).card_subgroup_dvd_card
  rw [Theory.SpecificGroups.SymplecticFour.card_unipotent, F.card_eq, ← pow_mul,
    ← Nat.card_congr e.toEquiv] at hd
  have hb := power_bound hc hd
  have he : F.degree = 2 := by omega
  have ho : Nat.card L = (2 ^ F.degree)^4 * ((2 ^ F.degree)^2 - 1) *
      ((2 ^ F.degree)^4 - 1) := by
    rw [Nat.card_congr e.toEquiv, Theory.SpecificGroups.SymplecticFour.card_sp, F.card_eq]
  rcases hc with hc | hc <;> norm_num [hc, he] at ho

/-- The defining two-subgroup already excludes every larger-field G₂ row. -/
theorem no_g2 (hc : Nat.card L = 20160 ∨ Nat.card L = 9999360)
    (F : BinaryField) (hF : 1 < F.degree)
    (e : L ≃* Atlas.G2.Model F.Carrier) : False := by
  have hd := (Atlas.G2.unipotent (K := F.Carrier)).card_subgroup_dvd_card
  rw [Atlas.G2.card_unipotent, F.card_eq, ← pow_mul, ← Nat.card_congr e.toEquiv] at hd
  have hb := power_bound hc hd
  omega

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.BinaryBranch.SourceClassification.Recognition
