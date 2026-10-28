module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Orbits
public import BenderSuzuki.External.Huppert.XI.theorem_3_6
public import Theory.SpecificGroups.Janko1.Model.Certification
public import Theory.SpecificGroups.SL2.OddProjectiveNonsolvable
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# Centerlessness of the exact nonnormal component models

The four genuine alternatives of 1.2.1(3) are simple after quasisimplicity
excludes the solvable odd PSL₂ parameter. Their centers are therefore
trivial. All transports use the displayed multiplicative equivalences to
the matrix, Suzuki, and Janko carriers. The PSL₃(2) calculation separately
uses its canonical equivalence with the centerless SL₃(2).

This permits the projection-envelope argument to exclude every nonnormal
alternative uniformly. No comparison between unrelated model labels or
new order or simplicity certification is needed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.504 and 1144, Proposition 1.2.1(3) and the proof of 15.3.49(l).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin CFSG.Quasithin.Chapter1.Section02
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.OrbitClosure
variable {X : Type*} [Group X] [IsQuasisimple X]

private theorem centerless [IsSimpleGroup X] : center X = ⊥ := by
  rcases (inferInstance : (center X).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative X (center_eq_top_iff.mp h)).elim

theorem nonnormal_model_center_eq_bot (hm : NonnormalCComponentModel X) : center X = ⊥ := by
  let : IsSimpleGroup (X ⧸ center X) := IsQuasisimple.simple
  have : Nontrivial X := (QuotientGroup.mk'_surjective (center X)).nontrivial
  cases hm with
  | linear_even n hn hm =>
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
    have hfour : 4 ≤ Nat.card F := by
      rw [hF]
      exact show 2 ^ 2 ≤ 2 ^ n from Nat.pow_le_pow_right (by decide : 0 < 2) hn
    let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hfour
    let : IsSimpleGroup X := e.isSimpleGroup
    exact centerless
  | linear_prime p hp ho hm =>
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
    have hns : ¬ Group.IsSolvable PSL(2,F) := by
      intro hs
      let := hs
      exact Group.IsPerfect.not_isSolvable X
        (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)
    have hfour := Matrix.ProjectiveSpecialLinearGroup.card_gt_three_of_odd_of_not_isSolvable
      (hF.symm ▸ ho) hns
    let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hfour
    let : IsSimpleGroup X := e.isSimpleGroup
    exact centerless
  | suzuki m hm he =>
    obtain ⟨e⟩ := he
    let : IsSimpleGroup (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :=
      (BenderSuzuki.External.huppert_blackburn_XI_3_6 m (by omega)).1
    let : IsSimpleGroup X := e.isSimpleGroup
    exact centerless
  | janko he =>
    obtain ⟨e⟩ := he
    let : IsSimpleGroup X := e.isSimpleGroup
    exact centerless


omit [IsQuasisimple X] in
/-- Centerlessness for the actual binary projective plane group. -/
theorem linear_three_center_eq_bot
    (e : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) : center X = ⊥ := by
  have hz : center Matrix.PSL3Two.PSL = ⊥ := by
    apply eq_bot_of_card_eq
    rw [← Nat.card_congr (centerCongr Matrix.PSL3Two.equiv).toEquiv,
      Matrix.PSL3Two.center_eq_bot, card_bot]
  apply eq_bot_of_card_eq
  rw [Nat.card_congr (centerCongr e).toEquiv, hz, card_bot]

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.OrbitClosure
