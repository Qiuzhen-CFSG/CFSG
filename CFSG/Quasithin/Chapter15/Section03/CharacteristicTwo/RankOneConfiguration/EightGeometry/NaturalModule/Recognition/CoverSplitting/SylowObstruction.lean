module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.Models
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Sylow

/-!
# The Sylow fixed-space obstruction in the augmentation module

Every Sylow two-subgroup of S₈ is transitive on its eight letters: a Sylow
containing an eight-cycle is transitive, and all Sylow subgroups are conjugate.
Thus every Sylow-fixed vector in the augmentation module is a constant function,
and is fixed by the whole symmetric group. On the other hand, orbit counting
forces every invariant binary plane to contain a nonzero Sylow-fixed vector.
These statements exclude an augmentation module with the moving line of 15.3.32.

The coordinates used by the last theorem must be equivariant for the whole
marked actor. Obtaining them from component coordinates is a separate step.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the covering
argument in 15.3.32(1), printed pp.1132–1133, using I.1.5–I.1.6(1), p.408.
-/

@[expose] public section

open scoped Pointwise
open Equiv Representation.BinaryOffender

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.CoverSplitting

theorem sylow_transitive (S : Sylow 2 (Perm (Fin 8))) (i j : Fin 8) :
    ∃ s ∈ (S : Subgroup (Perm (Fin 8))), s i = j := by
  have hc : Nat.card (Subgroup.zpowers (finRotate 8)) = 2 ^ 3 := by
    rw [Nat.card_zpowers, (isCycle_finRotate (n := 6)).orderOf, support_finRotate]
    rfl
  obtain ⟨Q, hQ⟩ := (IsPGroup.of_card hc).exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (Perm (Fin 8)) Q S
  have hmove : ∀ k : Fin 8, finRotate 8 k ≠ k := by decide
  obtain ⟨n, hn⟩ := (isCycle_finRotate (n := 6)).exists_pow_eq (hmove (g⁻¹ i)) (hmove (g⁻¹ j))
  refine ⟨g * finRotate 8 ^ n * g⁻¹, ?_, ?_⟩
  · exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj g) _
      (hQ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))
  · change g ((finRotate 8 ^ n) (g⁻¹ i)) = j
    rw [hn]
    simpa only [Perm.inv_def] using g.apply_symm_apply j

variable {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V]

theorem movingLine_fixed_ne_zero (ρ : Representation (ZMod 2) K V)
    {P S Y : Subgroup K} (line : Models.MovingLine ρ P S Y) (hS : IsPGroup 2 S) :
    ∃ v : V, v ∈ line.space ∧ v ∈ fixedSpace ρ S ∧ v ≠ 0 := by
  let : Finite line.space := Nat.finite_of_card_ne_zero (by rw [line.card]; decide)
  let : MulAction S line.space := {
    smul s v := ⟨ρ s v, line.sylow_stable s s.property v v.property⟩
    one_smul v := by apply Subtype.ext; change ρ 1 v = v; simp
    mul_smul s t v := by
      apply Subtype.ext
      exact LinearMap.congr_fun (ρ.map_mul s t) v }
  obtain ⟨v, hv, hnv⟩ := hS.exists_fixed_point_of_prime_dvd_card_of_fixed_point line.space
    (by rw [line.card]; decide) (a := 0) (by intro s; apply Subtype.ext; exact map_zero _)
  refine ⟨v, v.property, ?_, ?_⟩
  · intro s
    exact congrArg Subtype.val (hv s)
  · intro hz
    exact hnv (Subtype.ext hz.symm)

theorem movingLine_not_fixedSpace_le (ρ : Representation (ZMod 2) K V)
    {P S Y : Subgroup K} (line : Models.MovingLine ρ P S Y) (hS : IsPGroup 2 S) :
    ¬ fixedSpace ρ S ≤ fixedSpace ρ Y := by
  intro h
  obtain ⟨v, hv, hs, hn⟩ := movingLine_fixed_ne_zero ρ line hS
  exact hn (Submodule.disjoint_def.mp line.fixed_disjoint v hv (h hs))

variable [Finite K]

theorem core_sylow_fixed (e : K ≃* Perm (Fin 8)) (S : Sylow 2 K)
    (v : BinaryPermutation.core (Fin 8))
    (hv : ∀ s ∈ (S : Subgroup K), BinaryPermutation.coreRepresentation (Fin 8) (e s) v = v)
    (g : K) : BinaryPermutation.coreRepresentation (Fin 8) (e g) v = v := by
  have hconst : ∀ i j, (v : BinaryPermutation.Full (Fin 8)) i = v.val j := by
    intro i j
    obtain ⟨s, hs, hij⟩ := sylow_transitive (S.mapSurjective (f := e.toMonoidHom) e.surjective) i j
    obtain ⟨t, ht, rfl⟩ := hs
    have hfix := congrArg (fun w : BinaryPermutation.core (Fin 8) =>
      (w : BinaryPermutation.Full (Fin 8)) j) (hv t ht)
    change v.val ((e t).symm j) = v.val j at hfix
    change (e t) i = j at hij
    rw [← hij, Equiv.symm_apply_apply] at hfix
    exact hfix.trans (congrArg v.val hij)
  apply Subtype.ext
  ext i
  exact hconst _ _

theorem no_movingLine_core_coordinates (ρ : Representation (ZMod 2) K V)
    (e : K ≃* Perm (Fin 8)) (S : Sylow 2 K) {P Y : Subgroup K}
    (line : Models.MovingLine ρ P (S : Subgroup K) Y)
    (f : V ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 8))
    (hf : ∀ g v, f (ρ g v) = BinaryPermutation.coreRepresentation (Fin 8) (e g) (f v)) : False := by
  apply movingLine_not_fixedSpace_le ρ line S.isPGroup'
  intro v hv y
  apply f.injective
  change f (ρ y v) = f v
  rw [hf]
  apply core_sylow_fixed e S
  intro s hs
  rw [← hf]
  exact congrArg f (hv ⟨s, hs⟩)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.CoverSplitting

end
