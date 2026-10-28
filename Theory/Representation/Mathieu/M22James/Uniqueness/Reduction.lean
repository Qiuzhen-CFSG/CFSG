module

public import Theory.Representation.Mathieu.M22James.Irreducible
import Mathlib.Tactic.NoncommRing

/-!
# Central action and point-stabilizer comparison for 3.M₂₂ modules

On any faithful irreducible binary module the distinguished central scalar
has no fixed vectors and satisfies X² + X + 1 = 0. Schur's lemma makes its
displacement injective, and the order-three relation then gives the quadratic
identity. This argument does not assume uniqueness or a dimension bound.

The subgroup used for restriction is the full preimage of a point stabilizer
in the actual degree-22 Mathieu action. Its index is 22 and its order is
60480. Coordinate transport turns an equivalence on this subgroup into
literal agreement of actions on the fixed space `BinarySpace`. Finally, a
linear equivalence intertwining the two certified generators intertwines
the entire triple cover.

These are preliminaries for James (1973), Lemma 8.3, as used in
Aschbacher–Smith H.12.1(1), printed pp.393–394. Recognition of the restricted
module and rigidity of its extension remain separate proof obligations.
-/

@[expose] public section
noncomputable section

namespace Sporadic.Mathieu.M22TripleCover.Uniqueness

open Representation
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel

section CentralAction

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) M22TripleCover W) [ρ.IsIrreducible]

private theorem scalar_sub_one_injective (hf : Function.Injective ρ) :
    Function.Injective (ρ scalar - 1 : Module.End (ZMod 2) W) := by
  let f : ρ.IntertwiningMap ρ :=
    IntertwiningMap.centralMul ρ scalar scalar_mem_center - 1
  rcases IsIrreducible.injective_or_eq_zero f with hi | hz
  · exact hi
  · have he := congrArg IntertwiningMap.toLinearMap hz
    change ρ scalar - 1 = 0 at he
    have hs : scalar = 1 := hf ((sub_eq_zero.mp he).trans ρ.map_one.symm)
    exact False.elim (coreScalar_ne_one hs)

/-- The actual central scalar satisfies the same quadratic identity in every
faithful irreducible binary module. -/
theorem scalar_quadratic (hf : Function.Injective ρ) :
    ρ scalar ^ 2 + ρ scalar + 1 = 0 := by
  have hp : ρ scalar ^ 3 = 1 := by
    rw [← map_pow, coreScalar_pow_three, map_one]
  have hzero : (ρ scalar - 1) * (ρ scalar ^ 2 + ρ scalar + 1) = 0 := by
    calc
      _ = ρ scalar ^ 3 - 1 := by noncomm_ring
      _ = 0 := by rw [hp, sub_self]
  ext v
  apply scalar_sub_one_injective ρ hf
  change (ρ scalar - 1) ((ρ scalar ^ 2 + ρ scalar + 1 : Module.End (ZMod 2) W) v) =
    (ρ scalar - 1) 0
  rw [← Module.End.mul_apply, hzero, LinearMap.zero_apply, map_zero]

/-- The central scalar has no nonzero fixed vector in a faithful irreducible module. -/
theorem scalar_fixed_iff (hf : Function.Injective ρ) (v : W) :
    ρ scalar v = v ↔ v = 0 := by
  constructor
  · intro hv
    apply scalar_sub_one_injective ρ hf
    change ρ scalar v - v = ρ scalar 0 - 0
    rw [hv, sub_self, map_zero, sub_self]
  · rintro rfl
    exact map_zero _

end CentralAction

/-- The certified quotient map to the native Mathieu permutation group. -/
def quotientMap : M22TripleCover →* M22 :=
  corePermutationAction.codRestrict M22 fun g => by
    rw [← corePermutationAction_range_eq_M22]
    exact ⟨g, rfl⟩

theorem quotientMap_surjective : Function.Surjective quotientMap := by
  intro g
  have hg : (g : Equiv.Perm (Fin 22)) ∈ corePermutationAction.range := by
    rw [corePermutationAction_range_eq_M22]
    exact g.property
  obtain ⟨x, hx⟩ := hg
  exact ⟨x, Subtype.ext hx⟩

theorem quotientMap_ker : quotientMap.ker = Subgroup.center M22TripleCover := by
  rw [← corePermutationAction_ker_eq_center]
  ext g
  change quotientMap g = 1 ↔ corePermutationAction g = 1
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/-- The full preimage of the stabilizer of point 1 in the native degree-22 action. -/
def pointStabilizer : Subgroup M22TripleCover :=
  (MulAction.stabilizer M22 (1 : Fin 22)).comap quotientMap

theorem mem_pointStabilizer (g : M22TripleCover) :
    g ∈ pointStabilizer ↔ corePermutationAction g 1 = 1 := Iff.rfl

theorem pointStabilizer_index : pointStabilizer.index = 22 := by
  let : MulAction.IsPretransitive M22 (Fin 22) := m22_isPretransitive
  rw [pointStabilizer, Subgroup.index_comap_of_surjective _ quotientMap_surjective,
    MulAction.index_stabilizer_of_transitive]
  simp

theorem pointStabilizer_card : Nat.card pointStabilizer = 60480 := by
  have h := pointStabilizer.card_mul_index
  rw [pointStabilizer_index, card] at h
  omega

theorem scalar_mem_pointStabilizer : scalar ∈ pointStabilizer := by
  have h : corePermutationAction scalar = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [corePermutationAction_ker_eq_center]
    exact scalar_mem_center
  rw [mem_pointStabilizer, h]
  rfl

/-- Restriction of the constructed binary module to the actual point stabilizer. -/
def pointRepresentation : Representation (ZMod 2) pointStabilizer BinarySpace :=
  binaryRepresentation.comp pointStabilizer.subtype

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) M22TripleCover W)

/-- Express an action in specified binary coordinates. -/
def coordinateRepresentation (e : W ≃ₗ[ZMod 2] BinarySpace) :
    Representation (ZMod 2) M22TripleCover BinarySpace where
  toFun g := e.conj (ρ g)
  map_one' := by
    ext v
    simp [LinearEquiv.conj_apply]
  map_mul' g h := by
    ext v
    simp [LinearEquiv.conj_apply, map_mul]

/-- Coordinate transport includes its intertwining linear equivalence. -/
def coordinateEquiv (e : W ≃ₗ[ZMod 2] BinarySpace) :
    ρ.Equiv (coordinateRepresentation ρ e) :=
  .mk e (by
    intro g
    ext v
    simp [coordinateRepresentation, LinearEquiv.conj_apply])

theorem coordinateRepresentation_faithful (hf : Function.Injective ρ)
    (e : W ≃ₗ[ZMod 2] BinarySpace) :
    Function.Injective (coordinateRepresentation ρ e) := by
  intro g h he
  exact hf (e.conj.injective he)

theorem coordinateRepresentation_irreducible [ρ.IsIrreducible]
    (e : W ≃ₗ[ZMod 2] BinarySpace) :
    (coordinateRepresentation ρ e).IsIrreducible := by
  let f := IntertwiningMap.equivLinearMapAsModule ρ (coordinateRepresentation ρ e)
    (coordinateEquiv ρ e).toIntertwiningMap
  let ef := LinearEquiv.ofBijective f (show Function.Bijective f from e.bijective)
  rw [irreducible_iff_isSimpleModule_asModule]
  exact ef.isSimpleModule_iff.mp inferInstance

/-- A genuine equivalence on the point stabilizer gives literal equality of the
restricted matrices after coordinate transport. -/
theorem coordinateRepresentation_on_pointStabilizer
    (e : Representation.Equiv (ρ.comp pointStabilizer.subtype) pointRepresentation)
    (g : pointStabilizer) :
    coordinateRepresentation ρ e.toLinearEquiv g = binaryRepresentation g := by
  apply LinearMap.ext
  intro v
  change e (ρ g (e.symm v)) = binaryRepresentation g v
  have h := LinearMap.congr_fun (e.isIntertwining' g) (e.symm v)
  change e (ρ g (e.symm v)) = binaryRepresentation g (e (e.symm v)) at h
  simpa only [Representation.Equiv.apply_symm_apply] using h

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  (σ : Representation (ZMod 2) M22TripleCover U)

/-- Intertwining the two generating even words suffices for the whole group. -/
def equivOfGenerators (e : W ≃ₗ[ZMod 2] U)
    (ha : ∀ v, e (ρ coreGeneratorA v) = σ coreGeneratorA (e v))
    (hb : ∀ v, e (ρ coreGeneratorB v) = σ coreGeneratorB (e v)) :
    ρ.Equiv σ := by
  let τ : Representation (ZMod 2) M22TripleCover U := {
    toFun g := e.conj (ρ g)
    map_one' := by ext v; simp [LinearEquiv.conj_apply]
    map_mul' g h := by ext v; simp [LinearEquiv.conj_apply, map_mul] }
  have heq : τ = σ := by
    apply MonoidHom.eq_of_eqOn_dense coreGenerators_closure_eq_top
    rintro g (rfl | rfl)
    · ext v
      change e (ρ coreGeneratorA (e.symm v)) = σ coreGeneratorA v
      rw [ha, e.apply_symm_apply]
    · ext v
      change e (ρ coreGeneratorB (e.symm v)) = σ coreGeneratorB v
      rw [hb, e.apply_symm_apply]
  refine .mk e ?_
  intro g
  apply LinearMap.ext
  intro v
  change e (ρ g v) = σ g (e v)
  have h := LinearMap.congr_fun (DFunLike.congr_fun heq g) (e v)
  change e (ρ g (e.symm (e v))) = σ g (e v) at h
  simpa only [e.symm_apply_apply] using h

end Sporadic.Mathieu.M22TripleCover.Uniqueness
