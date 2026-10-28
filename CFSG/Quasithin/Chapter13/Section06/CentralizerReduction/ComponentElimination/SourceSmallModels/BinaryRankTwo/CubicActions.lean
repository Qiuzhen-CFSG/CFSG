module

public import Theory.Representation.G2BinaryParabolicFixed
public import Theory.Representation.BinaryPermutation.OffenderFixedSpace
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.Canonical

/-!
# Cubic actions in the binary rank-two branches of 13.6.22

The double three-cycle in A₆ fixes only zero on the actual augmentation
quotient. A fixed representative differs from its translate by a constant;
the cubic relation and even augmentation make the representative constant.
For G₂(2), the specified cubic `rootF 1 * weylS` acts in the six off-diagonal
octonion coordinates by three copies of (x,y) ↦ (x+y,x), hence fixes only zero.
Both elements belong to the actual two-residuals of the stated parabolics.
The G₂ statement retains the genuine derived carrier and scalar quotient.

These are concrete action calculations, not parabolic recognition from the
source's invariant four-group. That recognition remains a separate step.
Root conventions and license attribution are inherited from the ATLAS port
through `G2BinaryParabolicFixed` and `BinaryParabolicPair.ResidualAction`.
Source: Aschbacher–Smith, combined manuscript, Lemma 13.6.22, pp.932–933.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open Atlas.G2 Atlas.G2.Explicit Atlas.G2.Natural Atlas.G2.BinaryCore
open Atlas.G2.BinaryParabolicPair

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo.G2Action

private theorem cubic_apply (x : Atlas.SplitOctonion.Carrier (ZMod 2)) :
    cubicActor.val x =
      ![x 0+x 1, x 0, x 2+x 3+x 4+x 5,
        x 4+x 2, x 3+x 2, x 2, x 6+x 7, x 6] := by
  ext i
  fin_cases i <;>
    simp [cubicActor, shortRoot, rootF, rootFEquiv, rootFLinear, rootFApply,
      weylS, weylSEquiv, weylSLinear, weylSApply,
      sub_eq_add_neg, CharTwo.neg_eq] <;> ring

theorem coordinates_cubic (v : Space (ZMod 2)) :
    binaryCoordinates (ZMod 2) (action (ZMod 2) cubicActor v) =
      ![binaryCoordinates (ZMod 2) v 0 + binaryCoordinates (ZMod 2) v 1,
        binaryCoordinates (ZMod 2) v 0,
        binaryCoordinates (ZMod 2) v 2 + binaryCoordinates (ZMod 2) v 3,
        binaryCoordinates (ZMod 2) v 2,
        binaryCoordinates (ZMod 2) v 4 + binaryCoordinates (ZMod 2) v 5,
        binaryCoordinates (ZMod 2) v 4] := by
  obtain ⟨x,rfl⟩ := mk_surjective (ZMod 2) v
  have ht : x.val 3 + x.val 4 = 0 := x.property
  simp only [action_mk, binaryCoordinates_mk, traceZeroAction_val, cubic_apply]
  ext i
  fin_cases i <;> simp
  linear_combination ht

theorem cubic_fixed_eq_zero (v : Space (ZMod 2))
    (hv : action (ZMod 2) cubicActor v = v) : v = 0 := by
  have h := coordinates_cubic v
  rw [hv] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  have h5 := congrFun h 5
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at *
  have hz0 : binaryCoordinates (ZMod 2) v 0 = 0 := by linear_combination -h0 - h1
  have hz1 : binaryCoordinates (ZMod 2) v 1 = 0 := by linear_combination -h0
  have hz2 : binaryCoordinates (ZMod 2) v 2 = 0 := by linear_combination -h2 - h3
  have hz3 : binaryCoordinates (ZMod 2) v 3 = 0 := by linear_combination -h2
  have hz4 : binaryCoordinates (ZMod 2) v 4 = 0 := by linear_combination -h4 - h5
  have hz5 : binaryCoordinates (ZMod 2) v 5 = 0 := by linear_combination -h4
  apply (binaryCoordinates_injective (ZMod 2))
  rw [map_zero]
  ext i
  fin_cases i
  · exact hz0
  · exact hz1
  · exact hz2
  · exact hz3
  · exact hz4
  · exact hz5
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo.G2Action

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo.G2Action

theorem conjugate_fixed_eq_zero {A W : Type*} [Group A]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) (a : A)
    (ha : ∀ w, ρ a w = w → w = 0) (g : A) (w : W)
    (hw : ρ (g * a * g⁻¹) w = w) : w = 0 := by
  have hc : ρ a (ρ g⁻¹ w) = ρ g⁻¹ w := by
    have hh := congrArg (ρ g⁻¹) hw
    simpa only [map_mul, Module.End.mul_apply, ρ.inv_self_apply] using hh
  have hz := congrArg (ρ g) (ha _ hc)
  simpa only [ρ.self_inv_apply, map_zero] using hz

theorem g2_conjugate_cubic_fixed_eq_zero (g : Model (ZMod 2))
    (w : Space (ZMod 2))
    (hw : action (ZMod 2) (g * cubicActor * g⁻¹) w = w) : w = 0 :=
  conjugate_fixed_eq_zero (action (ZMod 2)) cubicActor cubic_fixed_eq_zero g w hw

theorem g2_residual_fixed_eq_zero (w : Space (ZMod 2))
    (hw : ∀ d ∈ ResidualAction.K, action (ZMod 2) d w = w) : w = 0 :=
  cubic_fixed_eq_zero w (hw _ ResidualAction.cubic_mem)

theorem g2_derived_residual_fixed_eq_zero (w : Space (ZMod 2))
    (hw : ∀ d ∈ (pResidual 2 derivedFirst).map derivedFirst.subtype,
      derivedAction (ZMod 2) d w = w) : w = 0 := by
  apply cubic_fixed_eq_zero
  exact hw ⟨cubicActor, cubicActor_mem_derived⟩
    ⟨⟨⟨cubicActor, cubicActor_mem_derived⟩, cubicActor_mem_derivedFirst⟩,
      cubicActor_derived_residual, rfl⟩
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo.G2Action

open BinaryPermutation Subgroup
open Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo.AlternatingAction

def cubic : Equiv.Perm (Fin 6) :=
  Equiv.swap 0 2 * Equiv.swap 2 4 * (Equiv.swap 1 3 * Equiv.swap 3 5)

theorem cubic_even : cubic ∈ alternatingGroup (Fin 6) := by decide +kernel
theorem cubic_cube : cubic ^ 3 = 1 := by decide +kernel

private theorem coordinates_fixed : ∀ x : Fin 6 → ZMod 2, ∀ c : ZMod 2,
    (∑ i, x i) = 0 → (∀ i, x (cubic.symm i) - x i = c) →
    ∀ i, x i = x 0 := by decide +kernel

theorem cubic_fixed_eq_zero (v : natural (Fin 6))
    (hv : naturalRepresentation (Fin 6) cubic v = v) : v = 0 := by
  obtain ⟨x, rfl⟩ := coreToNatural_surjective v
  have hd := congrArg Subtype.val hv
  obtain ⟨c, hc⟩ := (deleted_fixed_iff cubic x.val).mp hd
  have hx := coordinates_fixed x.val c x.property hc
  apply Subtype.ext
  change (constants (Fin 6)).mkQ x.val = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact (mem_constants_iff x.val).mpr ⟨x.val 0, hx⟩

theorem cubic_mem_syntheme_residual :
    cubic ∈ (pResidual 2 Theory.SpecificGroups.SymmetricSix.synthemeStabilizer).map
      Theory.SpecificGroups.SymmetricSix.synthemeStabilizer.subtype := by
  rw [residual_syntheme]
  decide +kernel
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo.AlternatingAction

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo.AlternatingAction

def actor : alternatingGroup (Fin 6) := ⟨cubic, cubic_even⟩
def parabolic : Subgroup (alternatingGroup (Fin 6)) :=
  Theory.SpecificGroups.SymmetricSix.synthemeStabilizer.subgroupOf _

theorem actor_mem_parabolic : actor ∈ parabolic := by
  change cubic ∈ Theory.SpecificGroups.SymmetricSix.synthemeStabilizer
  decide +kernel

theorem actor_mem_residual : actor ∈ (pResidual 2 parabolic).map parabolic.subtype := by
  refine ⟨⟨actor, actor_mem_parabolic⟩, ?_, rfl⟩
  apply Subgroup.mem_pResidual_of_orderOf_coprime
  have ho : orderOf (⟨actor, actor_mem_parabolic⟩ : parabolic) = 3 := by
    apply orderOf_eq_prime
    · exact Subtype.ext (Subtype.ext cubic_cube)
    · intro hh
      have h := congrArg (fun g : parabolic => (g.val.val) 0) hh
      change (2 : Fin 6) = 0 at h
      contradiction
  rw [ho]
  decide

theorem alternating_residual_fixed_eq_zero (w : natural (Fin 6))
    (hw : ∀ d ∈ (pResidual 2 parabolic).map parabolic.subtype,
      alternatingNaturalRepresentation (Ω := Fin 6) d w = w) : w = 0 :=
  by
    have hc := hw actor actor_mem_residual
    change naturalRepresentation (Fin 6) cubic w = w at hc
    exact cubic_fixed_eq_zero w hc
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo.AlternatingAction
