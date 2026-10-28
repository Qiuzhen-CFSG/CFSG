module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases.Alternatives
public import Theory.Representation.PSL3Two.SmallModules
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Residuals
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.Representation.QuadraticDuality
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
/-!
# Displacement of the plane residual on doubled dual modules

Every binary plane is carried to the standard plane by an actual SL₃(2)
operator. Two elements of its genuine two-residual have no common nonzero
fixed vector on the natural module. Dual annihilation therefore gives full
displacement on the dual and on each of its two coordinate summands.
This works for every plane, independently of a coordinate orientation.

Source: the action calculation in Aschbacher–Smith, 15.3.23, printed p.1129,
with the dual layers of C.1.34(3), printed pp.136–137.
-/

@[expose] public section
open Subgroup Representation Matrix
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.ThreeLayer.Displacement
abbrev W := Fin 3 → ZMod 2
abbrev ρ := BinaryLinearThree.W

private def plane : Submodule (ZMod 2) W := LinearMap.ker (LinearMap.proj (2 : Fin 3))

private lemma plane_card : Nat.card plane = 4 := by
  change Nat.card {v : W // v 2 = 0} = 4
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private lemma linear_implemented (f : W ≃ₗ[ZMod 2] W) : ∃ g : SL, ∀ v, ρ g v = f v := by
  let E := equivGL.trans (Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W))
  obtain ⟨g, hg⟩ := E.surjective f
  refine ⟨g, fun v => ?_⟩
  have h := congrArg (fun k : W ≃ₗ[ZMod 2] W => k v) hg
  change (Matrix.GeneralLinearGroup.toLin (equivGL g) : Module.End (ZMod 2) W) v = f v at h
  rw [equivGL_apply] at h
  exact h

private lemma plane_coordinates (U : Submodule (ZMod 2) W) (hU : Nat.card U = 4) :
    ∃ g : SL, ∀ v, ρ g v ∈ U ↔ v ∈ plane := by
  have hd : Module.finrank (ZMod 2) plane = Module.finrank (ZMod 2) U := by
    have hp := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := plane)
    have hu := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := U)
    rw [plane_card, Nat.card_zmod] at hp
    rw [hU, Nat.card_zmod] at hu
    exact Nat.pow_right_injective (by decide : 1 < 2) (hp.symm.trans hu)
  let f := LinearEquiv.ofFinrankEq plane U hd
  obtain ⟨a, ha⟩ := Submodule.exists_linearEquiv_restrict_eq f
  obtain ⟨g, hg⟩ := linear_implemented a
  refine ⟨g, fun v => ?_⟩
  rw [hg]
  constructor
  · intro hv
    obtain ⟨u, hu⟩ := f.surjective ⟨a v, hv⟩
    have he : a (u : W) = a v := (ha u).symm.trans (congrArg Subtype.val hu)
    exact a.injective he ▸ u.property
  · intro hv
    rw [← ha ⟨v, hv⟩]
    exact (f ⟨v, hv⟩).property

private def a : SL := ⟨!![0,1,0;1,1,0;0,0,1], by decide⟩
private def b : SL := ⟨!![1,0,1;0,1,0;0,0,1], by decide⟩
private lemma a_mem : a ∈ lineA := by decide +kernel
private lemma b_mem : b ∈ lineA := by decide +kernel
private lemma fixed_test : ∀ v : W, ρ a v = v → ρ b v = v → v = 0 := by
  decide +kernel

private lemma line_fixed (v : W) (hv : ∀ g ∈ residual lineParabolicSL, ρ g v = v) : v = 0 := by
  exact fixed_test v (hv a (line_residual.symm ▸ a_mem))
    (hv b (line_residual.symm ▸ b_mem))

def stabilizer (U : Submodule (ZMod 2) W) : Subgroup SL :=
  MulAction.stabilizer SL (U : Set W)

lemma residual_fixed (U : Submodule (ZMod 2) W) (hU : Nat.card U = 4)
    (v : W) (hv : ∀ x ∈ residual (stabilizer U), ρ x v = v) : v = 0 := by
  obtain ⟨g, hg⟩ := plane_coordinates U hU
  have hP : lineParabolicSL.map (MulAut.conj g).toMonoidHom ≤ stabilizer U := by
    rintro _ ⟨a, ha, rfl⟩
    rw [stabilizer, MulAction.mem_stabilizer_set' (Set.toFinite _)]
    intro w hw
    have hw' : ρ g⁻¹ w ∈ plane := (hg _).mp (by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      exact hw)
    have ha' := (MulAction.mem_stabilizer_set' (Set.toFinite _)).mp ha hw'
    have ht := (hg (ρ a (ρ g⁻¹ w))).mpr ha'
    change ρ (g * a * g⁻¹) w ∈ U
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
    exact ht
  have hR : (residual lineParabolicSL).map (MulAut.conj g).toMonoidHom ≤
      residual (stabilizer U) := by
    rw [MarkedAutomorphisms.residual, map_embedded_pResidual]
    exact embedded_pResidual_mono 2 hP
  have hz : ρ g⁻¹ v = 0 := line_fixed _ (by
    intro a ha
    have he := hv _ (hR (mem_map_of_mem (MulAut.conj g).toMonoidHom ha))
    have hh := congrArg (ρ g⁻¹) he
    change ρ g⁻¹ (ρ (g * a * g⁻¹) v) = ρ g⁻¹ v at hh
    simpa only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel_left] using hh)
  have hh := congrArg (ρ g) hz
  simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply, map_zero] using hh

lemma dual_displacement (U : Submodule (ZMod 2) W) (hU : Nat.card U = 4) :
    Coinvariants.ker (ρ.dual.comp (residual (stabilizer U)).subtype) = ⊤ := by
  have hi : Representation.invariants (ρ.comp (residual (stabilizer U)).subtype) = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro v hv
    exact residual_fixed U hU v (fun x hx => hv ⟨x,hx⟩)
  change Coinvariants.ker (Representation.dual (ρ.comp (residual (stabilizer U)).subtype)) = ⊤
  rw [← dualAnnihilator_invariants (ρ.comp (residual (stabilizer U)).subtype), hi,
    Submodule.dualAnnihilator_bot]

open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases

private lemma copies_displacement {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) K V) (hσ : Coinvariants.ker σ = ⊤) (a : ℕ) :
    Coinvariants.ker (moduleCopies σ a) = ⊤ := by
  classical
  let D := Coinvariants.ker (moduleCopies σ a)
  have hs (i : Fin a) (v : V) : Pi.single i v ∈ D := by
    have hle : Coinvariants.ker σ ≤ D.comap (LinearMap.single (R := ZMod 2) (φ := fun _ : Fin a => V) i) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨g,w⟩, rfl⟩
      have hh := Coinvariants.sub_mem_ker (ρ := moduleCopies σ a) g (Pi.single i w)
      change Pi.single i (σ g w - w) ∈ D
      convert hh using 1
      ext j
      by_cases hj : j = i
      · subst j; simp [moduleCopies]
      · simp [moduleCopies, Pi.single_apply, hj]
    exact hle (hσ ▸ Submodule.mem_top)
  apply top_unique
  intro v _
  have hsum := D.sum_mem (fun i (_ : i ∈ Finset.univ) => hs i (v i))
  simpa only [Finset.univ_sum_single] using hsum

lemma dual_copies_displacement (U : Submodule (ZMod 2) W) (hU : Nat.card U = 4) :
    Coinvariants.ker ((DualCopies (ZMod 2) 2).comp (residual (stabilizer U)).subtype) = ⊤ :=
  copies_displacement _ (dual_displacement U hU) 2

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.ThreeLayer.Displacement
