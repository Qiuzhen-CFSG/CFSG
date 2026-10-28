module

public import Theory.Representation.G2.RestrictedModules.Steinberg.BinaryOrbit.Parameters
public import Theory.Representation.G2.RestrictedModules.Steinberg.BinaryOrbit.Norm
public import Theory.Representation.G2.RestrictedModules.Steinberg.BinaryOrbit.Regular

/-!
# The 64-vector binary orbit and its fixed line

The specified translates of the tensor seed are a basis of their literal span
in every characteristic-two field. Their sum is the seed. Restriction to the
actual prime-field unipotent group is its regular representation, so the common
fixed vectors of all six binary roots form exactly the seed line.

The norm is calculated directly from the natural root and Weyl formulas.
A nonzero kernel of the regular orbit map would have a nonzero p-group fixed
vector, contradicting that norm calculation. This proves independence without
assuming invariance under the full G₂ group or a Steinberg classification.

Source: GLS3, 2.8.6, 2.8.7 and Example 2.8.10(g); the level-two factor used
on printed pp. 354, 356–357 of *The Classification of Quasithin Groups*.
Full-group stability and identification with the irreducible orbit carrier
are separate obligations, owned by the enclosing Steinberg construction.
-/

public noncomputable section
open scoped BigOperators
namespace Atlas.G2.Restricted.Steinberg
variable (F : Type*) [Field F] [CharP F 2]

private theorem sum_prime_orbit :
    (∑ g : BinaryUnipotent, binaryUnipotentAction F g
      (ambientAction F (longestWeyl F) (seed F))) = seed F := by
  calc
    _ = ∑ t : BinaryIndex, binaryOrbitVector F t :=
      (Fintype.sum_equiv binaryIndexEquiv _ _ (binaryOrbitVector_eq F)).symm
    _ = seed F := sum_binaryOrbitVector F

/-- The 64 literal binary translates are linearly independent over F. -/
theorem binaryOrbitVector_linearIndependent : LinearIndependent F (binaryOrbitVector F) := by
  have hc : ringChar F ≠ 0 := by rw [ringChar.eq F 2]; decide
  have hp : IsPGroup (ringChar F) BinaryUnipotent := by
    rw [ringChar.eq F 2]
    exact binaryUnipotent_isTwoGroup
  have hn : (∑ g : BinaryUnipotent, binaryUnipotentAction F g
      (ambientAction F (longestWeyl F) (seed F))) ≠ 0 := by
    rw [sum_prime_orbit]
    exact seed_ne_zero F
  have hi := BinaryOrbit.Regular.independent_orbit hc hp
    (binaryUnipotentAction F) (ambientAction F (longestWeyl F) (seed F)) hn
  simpa only [Function.comp_def, ← binaryOrbitVector_eq] using hi.comp binaryIndexEquiv
    binaryIndexEquiv.injective

/-- A basis of the literal binary span, indexed by the six binary parameters. -/
def binaryBasis : Module.Basis BinaryIndex F (binarySpan F) :=
  Module.Basis.span (binaryOrbitVector_linearIndependent F)

@[simp] theorem binaryBasis_val (t : BinaryIndex) :
    (binaryBasis F t).val = binaryOrbitVector F t := Module.Basis.coe_span_apply _ _

/-- The binary span has dimension 64, without a full-group stability premise. -/
theorem finrank_binarySpan : Module.finrank F (binarySpan F) = 64 := by
  rw [binarySpan, finrank_span_eq_card (binaryOrbitVector_linearIndependent F)]
  simp [BinaryIndex]

theorem seed_mem_binarySpan : seed F ∈ binarySpan F := by
  rw [← sum_binaryOrbitVector F]
  exact Submodule.sum_mem _ fun t _ => Submodule.subset_span ⟨t, rfl⟩

/-- Simultaneous fixedness by all six actual binary root elements is exactly the seed line. -/
theorem binarySpan_fixed_roots_iff (v : Ambient F) (hv : v ∈ binarySpan F) :
    (ambientAction F (rootA 1) v = v ∧
      ambientAction F (rootB 1) v = v ∧
      ambientAction F (rootC 1) v = v ∧
      ambientAction F (rootD 1) v = v ∧
      ambientAction F (rootE 1) v = v ∧
      ambientAction F (rootF 1) v = v) ↔ ∃ c : F, v = c • seed F := by
  constructor
  · rintro ⟨hA, hB, hC, hD, hE, hF⟩
    have hc : ringChar F ≠ 0 := by rw [ringChar.eq F 2]; decide
    have hp : IsPGroup (ringChar F) BinaryUnipotent := by
      rw [ringChar.eq F 2]
      exact binaryUnipotent_isTwoGroup
    have hn : (∑ g : BinaryUnipotent, binaryUnipotentAction F g
        (ambientAction F (longestWeyl F) (seed F))) ≠ 0 := by
      rw [sum_prime_orbit]
      exact seed_ne_zero F
    have hs : Set.range (binaryOrbitVector F) = Set.range (fun g : BinaryUnipotent =>
        binaryUnipotentAction F g (ambientAction F (longestWeyl F) (seed F))) := by
      rw [show binaryOrbitVector F = (fun t => binaryUnipotentAction F (binaryIndexEquiv t)
        (ambientAction F (longestWeyl F) (seed F))) from funext (binaryOrbitVector_eq F)]
      exact binaryIndexEquiv.surjective.range_comp (fun g : BinaryUnipotent =>
        binaryUnipotentAction F g (ambientAction F (longestWeyl F) (seed F)))
    have hw : v ∈ Submodule.span F (Set.range fun g : BinaryUnipotent =>
        binaryUnipotentAction F g (ambientAction F (longestWeyl F) (seed F))) := by
      simpa only [binarySpan, hs] using hv
    obtain ⟨c, he⟩ := BinaryOrbit.Regular.fixed_span_orbit hc hp
      (binaryUnipotentAction F) (ambientAction F (longestWeyl F) (seed F)) hn v hw
      (binaryUnipotentAction_fixed F v hA hB hC hD hE hF)
    exact ⟨c, by simpa only [sum_prime_orbit] using he⟩
  · rintro ⟨c, rfl⟩
    obtain ⟨hA, hB, hC, hD, hE, hF⟩ := seed_fixed_roots F 1
    simp only [map_smul, hA, hB, hC, hD, hE, hF, and_self]

end Atlas.G2.Restricted.Steinberg
