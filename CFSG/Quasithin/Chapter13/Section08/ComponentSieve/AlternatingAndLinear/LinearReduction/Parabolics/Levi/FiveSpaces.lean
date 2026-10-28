module

public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.Residuals.FlagTypes
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.FiveFlags
public import Theory.GroupTheory.PResidual.Defs

/-!
# The actual 2+3 and 3+2 parabolics in binary five-space

The singleton-cut flag stabilizers map onto the two diagonal linear groups,
with exact intrinsic two-core kernels. Finite-dimensional coordinates give
actual quotient equivalences S₃ × PSL₃(2) and PSL₃(2) × S₃. The last two
formulas specify which subquotient action is the marked S₃ factor.

The ambient single-node two-residual is also defined here, using O² rather
than the two-core or solvable residual. Its normalizer and its image in the
marked factors require further geometric calculations.

Source: Aschbacher–Smith 13.8.25, combined manuscript of 1 March 2004,
printed pp.959–960 (PDF pp.976–977).
-/

@[expose] public section

open Subgroup BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
open BinaryLinear.SmallParabolicLevi
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

/-- The ambient image of the two-residual of the marked single-node parabolic. -/
noncomputable def fiveNodeResidual (b : FiveBasis) (i : Fin 4) : Subgroup (LinearGroup 5) :=
  (pResidual 2 (fiveParabolic b {i})).map (fiveParabolic b {i}).subtype

theorem fiveNodeResidual_le (b : FiveBasis) (i : Fin 4) :
    fiveNodeResidual b i ≤ fiveParabolic b {i} := by
  exact (map_le_range _ _).trans_eq (range_subtype _)

/-- The singleton-cut stabilizer is the literal geometric subspace stabilizer. -/
noncomputable def fiveCutStabilizerEquiv (b : FiveBasis) (i : Fin 4) :
    flagStabilizer b {i} ≃* parabolic (flagSpace b i) :=
  MulEquiv.subgroupCongr (flagStabilizer_singleton b i)

@[simp] theorem fiveCutStabilizerEquiv_coe (b : FiveBasis) (i : Fin 4)
    (g : flagStabilizer b {i}) : (fiveCutStabilizerEquiv b i g).val = g.val := rfl

/-- The two actions of the singleton-cut flag stabilizer. -/
noncomputable def fiveCutBlockAction (b : FiveBasis) (i : Fin 4) :
    flagStabilizer b {i} →* BinaryLinear.GL (flagSpace b i) × BinaryLinear.GL (Space 5 ⧸ flagSpace b i) :=
  (blockAction (flagSpace b i)).comp (fiveCutStabilizerEquiv b i).toMonoidHom

theorem fiveCutBlockAction_surjective (b : FiveBasis) (i : Fin 4) :
    Function.Surjective (fiveCutBlockAction b i) :=
  (blockAction_surjective _).comp (fiveCutStabilizerEquiv b i).surjective

theorem ker_fiveCutBlockAction (b : FiveBasis) (i : Fin 4) :
    (fiveCutBlockAction b i).ker = pCore 2 (flagStabilizer b {i}) := by
  have hc := pCore_map_iso 2 (fiveCutStabilizerEquiv b i)
  ext g
  change blockAction (flagSpace b i) (fiveCutStabilizerEquiv b i g) = 1 ↔ _
  rw [← MonoidHom.mem_ker, ker_blockAction_eq_twoCore, ← hc]
  simp only [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

/-- The quotient equivalence records both actual subquotient actions. -/
noncomputable def fiveCutQuotientEquiv (b : FiveBasis) (i : Fin 4) :
    (flagStabilizer b {i} ⧸ pCore 2 (flagStabilizer b {i})) ≃*
      BinaryLinear.GL (flagSpace b i) × BinaryLinear.GL (Space 5 ⧸ flagSpace b i) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_fiveCutBlockAction b i).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (fiveCutBlockAction_surjective b i))

@[simp] theorem fiveCutQuotientEquiv_mk (b : FiveBasis) (i : Fin 4)
    (g : flagStabilizer b {i}) :
    fiveCutQuotientEquiv b i (QuotientGroup.mk' _ g) = fiveCutBlockAction b i g := rfl

noncomputable def fiveCutCoordinates (b : FiveBasis) (i : Fin 4) :
    flagSpace b i ≃ₗ[ZMod 2] Space (i.val + 1) :=
  LinearEquiv.ofFinrankEq _ _ (by rw [finrank_flagSpace, Module.finrank_fin_fun])

noncomputable def fiveQuotientCoordinates (b : FiveBasis) (i : Fin 4) :
    (Space 5 ⧸ flagSpace b i) ≃ₗ[ZMod 2] Space (4 - i.val) :=
  LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_fin_fun]
    have hd := (flagSpace b i).finrank_quotient_add_finrank
    rw [finrank_flagSpace, Module.finrank_fin_fun] at hd
    omega)

/-- The actual two-space stabilizer modulo its two-core is S₃ × PSL₃(2). -/
noncomputable def fiveTwoSpaceQuotientEquiv (b : FiveBasis) :
    (flagStabilizer b {1} ⧸ pCore 2 (flagStabilizer b {1})) ≃*
      Equiv.Perm (Fin 3) × Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) :=
  (fiveCutQuotientEquiv b 1).trans
    (((linearGroupCongr (fiveCutCoordinates b 1)).trans linearTwoEquivSymmetricThree).prodCongr
     ((linearGroupCongr (fiveQuotientCoordinates b 1)).trans linearThreeEquivProjective))

/-- The actual three-space stabilizer modulo its two-core is PSL₃(2) × S₃. -/
noncomputable def fiveThreeSpaceQuotientEquiv (b : FiveBasis) :
    (flagStabilizer b {2} ⧸ pCore 2 (flagStabilizer b {2})) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) × Equiv.Perm (Fin 3) :=
  (fiveCutQuotientEquiv b 2).trans
    (((linearGroupCongr (fiveCutCoordinates b 2)).trans linearThreeEquivProjective).prodCongr
     ((linearGroupCongr (fiveQuotientCoordinates b 2)).trans linearTwoEquivSymmetricThree))

/-- The S₃ coordinate of the two-space stabilizer is its action on that two-space. -/
theorem fiveTwoSpaceQuotientEquiv_fst_mk (b : FiveBasis)
    (g : flagStabilizer b {1}) :
    (fiveTwoSpaceQuotientEquiv b (QuotientGroup.mk' _ g)).1 =
      linearTwoEquivSymmetricThree (linearGroupCongr (fiveCutCoordinates b 1)
        (subspaceAction (flagSpace b 1) (fiveCutStabilizerEquiv b 1 g))) := rfl

/-- The S₃ coordinate of the three-space stabilizer is its action on the two-dimensional quotient. -/
theorem fiveThreeSpaceQuotientEquiv_snd_mk (b : FiveBasis)
    (g : flagStabilizer b {2}) :
    (fiveThreeSpaceQuotientEquiv b (QuotientGroup.mk' _ g)).2 =
      linearTwoEquivSymmetricThree (linearGroupCongr (fiveQuotientCoordinates b 2)
        (quotientAction (flagSpace b 2) (fiveCutStabilizerEquiv b 2 g))) := rfl

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

end
