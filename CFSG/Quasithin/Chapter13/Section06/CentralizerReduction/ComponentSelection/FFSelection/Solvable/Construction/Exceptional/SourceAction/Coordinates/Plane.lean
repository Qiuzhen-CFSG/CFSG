module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Exceptional.SourceAction.Coordinates.Projections
public import Theory.Representation.BinaryPermutationMulAction
public import Theory.GroupTheory.SpecificGroups.KleinFourAut

/-!
# Binary plane actions as three-point permutation actions

The natural binary S₃-module has four vectors. Its faithful permutation
action fills the automorphism group of its additive Klein four-group, whose
order is six. Conjugating any binary plane action through a linear equivalence
therefore produces a three-point permutation homomorphism, preserving the
whole action and its kernel. The cubic-coordinate construction consumes it.

Source: Aschbacher–Smith, B.5.7, printed p.106, the cubic moved plane.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional.SourceAction

private theorem natural_three_full :
    Function.Bijective (BinaryPermutation.naturalMulAction (Fin 3)) := by
  let e : BinaryPermutation.natural (Fin 3) ≃ₗ[ZMod 2] (ZMod 2 × ZMod 2) :=
    LinearEquiv.ofFinrankEq _ _ (by
      rw [BinaryPermutation.finrank_natural_odd _ (by decide)]
      simp [Module.finrank_prod])
  let : IsAddKleinFour (BinaryPermutation.natural (Fin 3)) := {
    card_four := by rw [Nat.card_congr e.toEquiv]; simp
    exponent_two := by
      rw [AddMonoid.exponent_eq_of_addEquiv e.toAddEquiv]
      exact IsAddKleinFour.exponent_two }
  apply (BinaryPermutation.naturalMulAction_injective_of_odd (Fin 3) (by decide)).bijective_of_nat_card_le
  rw [IsKleinFour.card_mulAut, Nat.card_eq_fintype_card, Fintype.card_perm]
  decide

/-- Every binary plane action has a three-point permutation coordinate,
with a linear intertwiner for the whole acting group. -/
theorem plane_permutation_coordinates {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    (σ : Representation (ZMod 2) G V) (hd : Module.finrank (ZMod 2) V = 2) :
    ∃ f : G →* Equiv.Perm (Fin 3),
      ∃ b : V ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 3),
        (∀ g w, b (σ g w) = BinaryPermutation.naturalRepresentation (Fin 3) (f g) (b w)) ∧
        (∀ g, f g = 1 ↔ σ g = 1) := by
  let b : V ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 3) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hd, BinaryPermutation.finrank_natural_odd _ (by decide)]; rfl)
  let τ : Representation (ZMod 2) G (BinaryPermutation.natural (Fin 3)) :=
    b.conjRingEquiv.toMonoidHom.comp σ
  let a : G →* MulAut (Multiplicative (BinaryPermutation.natural (Fin 3))) := {
    toFun g := (LinearEquiv.ofBijective (τ g) (τ.apply_bijective g)).toAddEquiv.toMultiplicative
    map_one' := by apply MulEquiv.ext; intro v; exact congrArg Multiplicative.ofAdd (LinearMap.congr_fun τ.map_one v.toAdd)
    map_mul' g h := by apply MulEquiv.ext; intro v; exact congrArg Multiplicative.ofAdd (LinearMap.congr_fun (τ.map_mul g h) v.toAdd) }
  let j := MulEquiv.ofBijective (BinaryPermutation.naturalMulAction (Fin 3)) natural_three_full
  let f : G →* Equiv.Perm (Fin 3) := j.symm.toMonoidHom.comp a
  have hact (g : G) (w : V) :
      b (σ g w) = BinaryPermutation.naturalRepresentation (Fin 3) (f g) (b w) := by
    have he : BinaryPermutation.naturalMulAction (Fin 3) (f g) = a g := j.apply_symm_apply (a g)
    have hh := congrArg (fun t => Multiplicative.toAdd (t (Multiplicative.ofAdd (b w)))) he
    change BinaryPermutation.naturalRepresentation (Fin 3) (f g) (b w) =
      b (σ g (b.symm (b w))) at hh
    rw [b.symm_apply_apply] at hh
    exact hh.symm
  refine ⟨f, b, hact, ?_⟩
  intro g
  constructor
  · intro hg
    apply LinearMap.ext
    intro w
    apply b.injective
    simpa [hg] using hact g w
  · intro hg
    apply j.injective
    rw [map_one]
    change j (j.symm (a g)) = 1
    rw [j.apply_symm_apply]
    apply MulEquiv.ext
    intro w
    change Multiplicative.ofAdd (b (σ g (b.symm w.toAdd))) = w
    simp [hg]

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional.SourceAction
