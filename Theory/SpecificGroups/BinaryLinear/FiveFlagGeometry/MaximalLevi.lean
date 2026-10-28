module

public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.MaximalOvergroups
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models

/-!
# Marked Levi quotients of the four maximal binary five-space parabolics

The actions on a flag space and its quotient have kernel equal to the
intrinsic two-core. Coordinates identify the two middle Levi quotients
with S₃ × PSL₃(2), and the endpoint quotients with PSL₄(2).
The common formula on representatives retains both geometric actions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.24, printed p.1130 (PDF p.1147).
-/

@[expose] public section

open Subgroup BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.SmallParabolicLevi
namespace BinaryLinear.FiveFlagGeometry.MaximalOvergroups

noncomputable def cutCoordinates (b : FiveBasis) (i : Fin 4) :
    flagSpace b i ≃ₗ[ZMod 2] Space (i.val + 1) :=
  LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_fin_fun]
    exact BinaryLinear.InvariantNodeActions.cutSpace_finrank b i)

noncomputable def quotientCoordinates (b : FiveBasis) (i : Fin 4) :
    (Space 5 ⧸ flagSpace b i) ≃ₗ[ZMod 2] Space (4 - i.val) :=
  LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_fin_fun]
    have hd := (flagSpace b i).finrank_quotient_add_finrank
    change Module.finrank (ZMod 2) (Space 5 ⧸ flagSpace b i) +
      Module.finrank (ZMod 2) (flagSpace b i) = Module.finrank (ZMod 2) (Space 5) at hd
    rw [show Module.finrank (ZMod 2) (flagSpace b i) = i.val + 1 from
      BinaryLinear.InvariantNodeActions.cutSpace_finrank b i, Module.finrank_fin_fun] at hd
    omega)

noncomputable def singletonEquiv (b : FiveBasis) (i : Fin 4) :
    flagStabilizer b {i} ≃* parabolic (flagSpace b i) :=
  MulEquiv.subgroupCongr (flagStabilizer_singleton b i)

noncomputable def singletonQuotientEquiv (b : FiveBasis) (i : Fin 4) :
    (flagStabilizer b {i} ⧸ pCore 2 (flagStabilizer b {i})) ≃*
      LinearGroup (i.val + 1) × LinearGroup (4 - i.val) :=
  (QuotientGroup.congr _ _ (singletonEquiv b i)
    (pCore_map_iso 2 (singletonEquiv b i))).trans
    (quotientTwoCoreEquivOfCoordinates (flagSpace b i) (cutCoordinates b i)
      (quotientCoordinates b i))

theorem singletonQuotientEquiv_mk (b : FiveBasis) (i : Fin 4)
    (g : flagStabilizer b {i}) :
    singletonQuotientEquiv b i (QuotientGroup.mk' _ g) =
      (linearGroupCongr (cutCoordinates b i) (subspaceAction _ (singletonEquiv b i g)),
       linearGroupCongr (quotientCoordinates b i) (quotientAction _ (singletonEquiv b i g))) := rfl

local instance : Unique (LinearGroup 1) :=
  { default := 1
    uniq := fun _g => (slEquivLinear 1).symm.injective (Subsingleton.elim _ _) }

noncomputable def lineQuotientEquiv (b : FiveBasis) :
    (flagStabilizer b {0} ⧸ pCore 2 (flagStabilizer b {0})) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2) :=
  (singletonQuotientEquiv b 0).trans
    ((MulEquiv.uniqueProd (N := LinearGroup 1) (M := LinearGroup 4)).trans
      (projectiveEquivLinear (by decide : 0 < 4)).symm)

noncomputable def hyperplaneQuotientEquiv (b : FiveBasis) :
    (flagStabilizer b {3} ⧸ pCore 2 (flagStabilizer b {3})) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2) :=
  (singletonQuotientEquiv b 3).trans
    ((MulEquiv.prodUnique (N := LinearGroup 1) (M := LinearGroup 4)).trans
      (projectiveEquivLinear (by decide : 0 < 4)).symm)

noncomputable def planeQuotientEquiv (b : FiveBasis) :
    (flagStabilizer b {1} ⧸ pCore 2 (flagStabilizer b {1})) ≃*
      Equiv.Perm (Fin 3) × Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) :=
  (singletonQuotientEquiv b 1).trans
    (linearTwoEquivSymmetricThree.prodCongr linearThreeEquivProjective)

noncomputable def threeSpaceQuotientEquiv (b : FiveBasis) :
    (flagStabilizer b {2} ⧸ pCore 2 (flagStabilizer b {2})) ≃*
      Equiv.Perm (Fin 3) × Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) :=
  (singletonQuotientEquiv b 2).trans
    ((linearThreeEquivProjective.prodCongr linearTwoEquivSymmetricThree).trans
      MulEquiv.prodComm)

/-- All four cuts retain their actual two-core quotient, including the
factor swap at a three-dimensional cut. -/
theorem singleton_quotient_models (b : FiveBasis) (i : Fin 4) :
    Nonempty ((flagStabilizer b {i} ⧸ pCore 2 (flagStabilizer b {i})) ≃*
      (Equiv.Perm (Fin 3) × Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))) ∨
    Nonempty ((flagStabilizer b {i} ⧸ pCore 2 (flagStabilizer b {i})) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) := by
  fin_cases i
  · exact Or.inr ⟨lineQuotientEquiv b⟩
  · exact Or.inl ⟨planeQuotientEquiv b⟩
  · exact Or.inl ⟨threeSpaceQuotientEquiv b⟩
  · exact Or.inr ⟨hyperplaneQuotientEquiv b⟩
end BinaryLinear.FiveFlagGeometry.MaximalOvergroups

end
