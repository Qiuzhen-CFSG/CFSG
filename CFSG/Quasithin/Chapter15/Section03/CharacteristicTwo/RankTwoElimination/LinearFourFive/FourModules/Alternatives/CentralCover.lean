module

public import Theory.Representation.BinaryOffender.Defs
public import Theory.GroupTheory.PPerfectHom
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.ModelCases

/-!
# Lifting fixed vectors through the central cover

If a two-perfect actor fixes a vector modulo the component-fixed space,
its displacements lie in a binary group on which it acts trivially.
The displacement map is then a homomorphism, and two-perfectness kills it.
Consequently the original vector is fixed as well. This proves the cover
step without splitting the module or discarding its fixed-space kernel.

The orthogonal corollary uses the actual equivariant quotient coordinates.
It leaves the calculation of quotient fixation to the marked parabolic
argument; it does not assert that that geometric hypothesis holds.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the
orthogonal-quotient exclusion in 15.3.24, printed p.1129.
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Alternatives

variable {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V]

/-- A binary displacement homomorphism vanishes on a two-perfect actor. -/
theorem fixed_of_displacement_fixed (ρ : Representation (ZMod 2) K V)
    (Y : Subgroup K) (hY : IsPPerfect 2 Y) (v : V)
    (h : ∀ y : Y, ρ y v - v ∈ fixedSpace ρ Y) :
    ∀ y : Y, ρ y v = v := by
  let δ : Y →* Multiplicative V := {
    toFun y := Multiplicative.ofAdd (ρ y v - v)
    map_one' := by simp
    map_mul' y z := by
      apply Multiplicative.toAdd.injective
      change ρ ((y : K) * z) v - v = (ρ y v - v) + (ρ z v - v)
      have hz : ρ y (ρ z v - v) = ρ z v - v := h z y
      rw [map_sub] at hz
      rw [map_mul, Module.End.mul_apply]
      calc
        _ = (ρ y (ρ z v) - ρ y v) + (ρ y v - v) := by abel
        _ = _ := by rw [hz]; abel }
  have hp : IsPGroup 2 (Multiplicative V) := by
    intro w
    refine ⟨1, ?_⟩
    apply Multiplicative.toAdd.injective
    change (2 ^ 1) • w.toAdd = 0
    calc
      (2 ^ 1) • w.toAdd = (2 : ZMod 2) • w.toAdd := by
        exact (Nat.cast_smul_eq_nsmul (R := ZMod 2) 2 w.toAdd).symm
      _ = 0 := by rw [show (2 : ZMod 2) = 0 from rfl, zero_smul]
  have hδ := hY.hom_eq_one_of_isPGroup hp δ
  intro y
  have hy := congrArg (fun f : Y →* Multiplicative V => (f y).toAdd) hδ
  exact sub_eq_zero.mp hy

/-- Fixation modulo component-fixed vectors lifts without a splitting assumption. -/
theorem fixed_of_fixedSpace_quotient (ρ : Representation (ZMod 2) K V)
    (Y L : Subgroup K) (hYL : Y ≤ L) (hY : IsPPerfect 2 Y) (v : V)
    (h : ∀ y : Y, (fixedSpace ρ L).mkQ (ρ y v) = (fixedSpace ρ L).mkQ v) :
    ∀ y : Y, ρ y v = v := by
  apply fixed_of_displacement_fixed ρ Y hY v
  intro y
  have hf : ρ y v - v ∈ fixedSpace ρ L := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change (fixedSpace ρ L).mkQ (ρ y v - v) = 0
    rw [map_sub, h y, sub_self]
  exact fun z => hf ⟨z, hYL z.property⟩

/-- Apply the cover argument to the actual orthogonal quotient and its own marking. -/
theorem fixed_of_orthogonal_projection (ρ : Representation (ZMod 2) K V)
    (Y L : Subgroup K) (hYL : Y ≤ L) (hY : IsPPerfect 2 Y)
    (h : RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.OrthogonalQuotient ρ L)
    (v : V)
    (hfix : ∀ y : Y, BinaryPermutation.naturalRepresentation (Fin 8)
      (h.model ⟨y, hYL y.property⟩).val (h.projection v) = h.projection v) :
    ∀ y : Y, ρ y v = v := by
  apply fixed_of_fixedSpace_quotient ρ Y L hYL hY v
  intro y
  apply h.coordinates.injective
  exact (h.equivariant ⟨y, hYL y.property⟩ v).trans (hfix y)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Alternatives
end
