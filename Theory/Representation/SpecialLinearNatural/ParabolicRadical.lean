module
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoBlocks
public import Theory.Representation.BinaryNaturalDual.FiveActors.Hyperplanes
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.Representation.SpecialLinearNatural
public import Theory.Representation.BinaryOffender.SubspaceAction
/-!
# Orders of binary special-linear parabolic radicals

The natural SLₙ(2) stabilizer is identified with the geometric stabilizer in
GL(V). Its intrinsic two-core is the group fixing P and V/P pointwise, which
is isomorphic to the additive group Hom(V/P,P). Thus its order is
2^((n - dim P) * dim P). For either end node of SL₅(2), the binary offender
rank is four.

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
B.4.2(11), printed p.86, and the exterior-square exclusion in G.6.4,
printed pp.345–346. The proof retains the actual natural stabilizer and
its embedded intrinsic two-core.
-/

open Subgroup Representation Representation.BinaryOffender BinaryLinear BinaryLinear.OuterCyclic
@[expose] public section
namespace Representation.SpecialLinearNatural

/-- The literal natural stabilizer in the matrix and linear-map models. -/
noncomputable def subspaceStabilizerEquiv (n : ℕ) (P : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    subspaceStabilizer (specialLinearNatural n) P ≃* parabolic P where
  toFun g := ⟨slEquivLinear n g.val, g.property⟩
  invFun g := ⟨(slEquivLinear n).symm g.val, by
    intro v
    change slEquivLinear n ((slEquivLinear n).symm g.val) v ∈ P ↔ v ∈ P
    rw [MulEquiv.apply_symm_apply]
    exact g.property v⟩
  left_inv g := Subtype.ext ((slEquivLinear n).symm_apply_apply g.val)
  right_inv g := Subtype.ext ((slEquivLinear n).apply_symm_apply g.val)
  map_mul' g h := Subtype.ext ((slEquivLinear n).map_mul g.val h.val)

/-- The geometric radical has the order of Hom(V/P,P). -/
theorem card_radical {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (P : Submodule (ZMod 2) V) :
    Nat.card (BinaryLinear.radical P) =
      2 ^ (Module.finrank (ZMod 2) (V ⧸ P) * Module.finrank (ZMod 2) P) := by
  rw [Nat.card_congr (BinaryNaturalDual.FiveActors.equiv P).toEquiv]
  change Nat.card ((V ⧸ P) →ₗ[ZMod 2] P) = _
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    Module.finrank_linearMap]

/-- Order of the intrinsic two-core, mapped into the original special linear group. -/
theorem card_subspaceStabilizer_twoCore (n : ℕ) (P : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Nat.card ((pCore 2 (subspaceStabilizer (specialLinearNatural n) P)).map
      (subspaceStabilizer (specialLinearNatural n) P).subtype) =
      2 ^ ((n - Module.finrank (ZMod 2) P) * Module.finrank (ZMod 2) P) := by
  rw [Subgroup.card_map_of_injective (subspaceStabilizer _ _).subtype_injective]
  have hcard : Nat.card (pCore 2 (subspaceStabilizer (specialLinearNatural n) P)) =
      Nat.card (pCore 2 (parabolic P)) := by
    rw [← pCore_map_iso 2 (subspaceStabilizerEquiv n P)]
    exact (Subgroup.card_map_of_injective (subspaceStabilizerEquiv n P).injective).symm
  rw [hcard]
  have hrad : Nat.card (pCore 2 (parabolic P)) = Nat.card (BinaryLinear.radical P) := by
    rw [← BinaryLinear.SmallParabolicLevi.map_twoCore_eq_radical P]
    exact (Subgroup.card_map_of_injective (parabolic P).subtype_injective).symm
  rw [hrad, card_radical]
  have hsum := Submodule.finrank_quotient_add_finrank P
  have hd : Module.finrank (ZMod 2) (Fin n → ZMod 2) = n := by simp
  rw [hd] at hsum
  congr 2
  omega

/-- Each of the two end-node radicals in SL₅(2) has binary rank four. -/
theorem endNode_five_rank (P : Submodule (ZMod 2) (Fin 5 → ZMod 2))
    (hP : Module.finrank (ZMod 2) P = 1 ∨ Module.finrank (ZMod 2) P = 4) :
    rank ((pCore 2 (subspaceStabilizer (specialLinearNatural 5) P)).map
      (subspaceStabilizer (specialLinearNatural 5) P).subtype) = 4 := by
  rw [rank, card_subspaceStabilizer_twoCore]
  rcases hP with hP | hP <;> rw [hP] <;> decide
end Representation.SpecialLinearNatural
