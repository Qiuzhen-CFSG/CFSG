module

public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.SylowOvergroups
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoNodes.Flags
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Three-free Sylow overgroups in the binary five-dimensional linear group

Every Sylow two-overgroup stabilizes a basis flag. A diagonal block of
dimension at least two has order divisible by three. If three does not divide
the overgroup order, all its diagonal groups are trivial, leaving the
two-group diagonal kernel.

Source: Aschbacher--Smith, A.3.15, printed pp.50--51, its characteristic-two
parabolic argument specialized to L₅(2).
-/

public section
open Subgroup
namespace BinaryLinear.FiveFlagGeometry
open OuterCyclic SmallParabolicLevi SmallParabolicLevi.TwoNodes

private noncomputable def blockCoordinates (c : Fin 5 → Fin 5) (k : Fin 5) :
    BlockSpace c k ≃ₗ[ZMod 2] Space (Nat.card (Block c k)) := by
  classical
  exact LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2)
    ((Fintype.equivFin (Block c k)).trans (finCongr Nat.card_eq_fintype_card.symm)).symm

private theorem block_group_card (c : Fin 5 → Fin 5) (k : Fin 5) :
    Nat.card (BinaryLinear.GL (BlockSpace c k)) =
      ∏ i : Fin (Nat.card (Block c k)),
        (2 ^ Nat.card (Block c k) - 2 ^ i.val) := by
  rw [Nat.card_congr (linearGroupCongr (blockCoordinates c k)).toEquiv,
    ← Nat.card_congr (matrixEquivLinear _).toEquiv, Matrix.card_GL_field]
  simp

private theorem block_card_le (c : Fin 5 → Fin 5) (k : Fin 5) :
    Nat.card (Block c k) ≤ 5 := by
  simpa using Nat.card_le_card_of_injective
    (Subtype.val : Block c k → Fin 5) Subtype.val_injective

/-- A flag stabilizer of order prime to three is a two-group. -/
theorem flag_isPGroup_of_not_three_dvd (b : FiveBasis) (cuts : Set (Fin 4))
    (h3 : ¬ 3 ∣ Nat.card (flagStabilizer b cuts)) :
    IsPGroup 2 (flagStabilizer b cuts) := by
  classical
  have hcard (k : Fin 5) : Nat.card (BinaryLinear.GL (BlockSpace (cutLabel cuts) k)) = 1 := by
    let f := Pi.evalMonoidHom
      (fun k : Fin 5 => BinaryLinear.GL (BlockSpace (cutLabel cuts) k)) k
    have hf : Function.Surjective f := by
      intro a
      exact ⟨Function.update 1 k a, Function.update_self ..⟩
    have hd := card_dvd_of_surjective (f.comp (flagDiagonalAction b cuts))
      (hf.comp (flagDiagonalAction_surjective b cuts))
    have hsmall := block_card_le (cutLabel cuts) k
    rw [block_group_card] at hd ⊢
    generalize Nat.card (Block (cutLabel cuts) k) = n at *
    have hn : n ≤ 1 := by
      by_contra hn
      have hn2 : 2 ≤ n := by omega
      have hdiv : 3 ∣ ∏ i : Fin n, (2 ^ n - 2 ^ i.val) := by
        interval_cases n <;> decide
      exact h3 (hdiv.trans hd)
    interval_cases n <;> decide
  have hk : (flagDiagonalAction b cuts).ker = ⊤ := by
    apply top_unique
    intro g _
    change flagDiagonalAction b cuts g = 1
    funext k
    have : Subsingleton (BinaryLinear.GL (BlockSpace (cutLabel cuts) k)) :=
      (Nat.card_eq_one_iff_unique.mp (hcard k)).1
    exact Subsingleton.elim _ _
  have hp : IsPGroup 2 (flagDiagonalAction b cuts).ker := by
    rw [ker_flagDiagonalAction]
    exact pCore_isPGroup
  rw [hk] at hp
  exact hp.of_equiv (Subgroup.topEquiv)

/-- A Sylow two-overgroup of order prime to three is itself a two-group. -/
theorem isPGroup_of_sylow_le_of_not_three_dvd
    (S : Sylow 2 (LinearGroup 5)) (P : Subgroup (LinearGroup 5))
    (hSP : (S : Subgroup (LinearGroup 5)) ≤ P)
    (h3 : ¬ 3 ∣ Nat.card P) : IsPGroup 2 P := by
  obtain ⟨b, cuts, rfl⟩ := isFlagParabolic_of_sylow_le S P hSP
  exact flag_isPGroup_of_not_three_dvd b cuts h3

end BinaryLinear.FiveFlagGeometry
