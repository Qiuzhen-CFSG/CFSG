module

public import Theory.SpecificGroups.Triality.StandardModel
public import Theory.SpecificGroups.Triality.LeviRankOneMatrices.Comparison

/-!
# Scalar rigidity of the split D4 Geck group in characteristic two

Every matrix in the generated split group fixes the Cartan vector `h₀ + h₂`.
Indeed, the arms 0 and 2 have identical adjacency, so their extra contributions
in each rank-one block cancel in characteristic two. The proved comparison
with the integral Geck curves gives this identity for the actual generators;
subgroup closure extends it to the whole split group. The vector has coordinate
1 at `h₀`, so a scalar matrix fixing it has scalar 1.

Thus the split group contains no nonidentity scalar matrix, for every parameter
of characteristic two, including `q = 2`. This supplies the scalar-rigidity
input to the elementary central-kernel argument; it does not assert that every
central element is scalar.

Source: GLS3 Theorem 2.2.6 and the kernel paragraph in the proof of
Theorems 2.3.4–5 (`refs/KGroup/GLS3/chapter2.tex`), using the integral Geck
realization and its pinned rank-one matrix formulas.
-/

@[expose] public section

open Matrix
open scoped MatrixGroups
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.SimpleGeckGroup
open Triality.Standard.Parabolics.RankOneMatrices

namespace Triality.Standard.ElementaryCentralKernel
noncomputable section
local instance scalarRigidityDecidableEq : DecidableEq LatticeIndex :=
  fun a b => instDecidableEqSum a b

variable {F : Type*} [CommRing F] [CharP F 2]

private def fixedCartanVector : LatticeIndex → F :=
  Pi.single (.inl (typeDRootPairing_baseEquiv 2 0)) 1 +
    Pi.single (.inl (typeDRootPairing_baseEquiv 2 2)) 1

private lemma latticeEquiv_cartan (i j : Fin 4) :
    latticeEquiv i (.inl (.inl j)) = .inl (typeDRootPairing_baseEquiv 2 j) := rfl

private lemma ambientHom_fixes (i : Fin 4) (A : SL(2, F)) :
    (ambientHom i A).val *ᵥ fixedCartanVector = fixedCartanVector := by
  funext r
  obtain ⟨r, rfl⟩ := (latticeEquiv i).surjective r
  simp only [fixedCartanVector, mulVec_add, mulVec_single_one, Pi.add_apply, col_apply]
  rw [← latticeEquiv_cartan i 0, ← latticeEquiv_cartan i 2,
    ambientHom_entry, ambientHom_entry]
  simp only [Pi.single_apply, (latticeEquiv i).injective.eq_iff]
  rcases r with (r | r) | r
  · fin_cases i <;> fin_cases r <;>
      simp [blockMatrix, specialBlock, adjacent, CharTwo.add_self_eq_zero]
  · fin_cases i <;>
      simp [blockMatrix, specialBlock, adjacent, CharTwo.add_self_eq_zero]
  · simp [blockMatrix]

private lemma geck_fixes_cartanVector
    (g : RootPairing.SimpleGeckGroup.Carrier (typeDRootPairing_base 2) F) :
    g.val.val *ᵥ fixedCartanVector = fixedCartanVector := by
  rcases g with ⟨g, hg⟩
  change g.val *ᵥ fixedCartanVector = fixedCartanVector
  change g ∈ Subgroup.closure _ at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨⟨s, i⟩, t, rfl⟩ := hx
    obtain ⟨i, rfl⟩ := (typeDRootPairing_baseEquiv 2).surjective i
    cases s
    · change (negativeUnit (typeDRootPairing_baseEquiv 2 i) t).val *ᵥ _ = _
      rw [← ambientHom_negative]
      exact ambientHom_fixes i _
    · change (positiveUnit (typeDRootPairing_baseEquiv 2 i) t).val *ᵥ _ = _
      rw [← ambientHom_positive]
      exact ambientHom_fixes i _
  | one => exact one_mulVec _
  | mul x y hx hy ihx ihy =>
    change (x.val * y.val) *ᵥ fixedCartanVector = fixedCartanVector
    rw [← mulVec_mulVec, ihy, ihx]
  | inv x hx ih =>
    change x⁻¹.val *ᵥ fixedCartanVector = fixedCartanVector
    calc
      x⁻¹.val *ᵥ fixedCartanVector = x⁻¹.val *ᵥ (x.val *ᵥ fixedCartanVector) := by rw [ih]
      _ = fixedCartanVector := by
        rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

/-- A scalar matrix in the actual split Geck group has scalar 1 in
characteristic two, with no restriction on the field exponent. -/
theorem split_scalar_eq_one (P : Parameters) (hp : P.prime = 2)
    (g : SplitGroup P) (c : ExtensionField P) (h : g.val.val = c • 1) : c = 1 := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  have hv := geck_fixes_cartanVector g
  rw [h, smul_mulVec, one_mulVec] at hv
  have hentry := congrFun hv (.inl (typeDRootPairing_baseEquiv 2 0))
  simpa [fixedCartanVector, Pi.single_apply, smul_eq_mul] using hentry

/-- The split D4 group contains no nonidentity scalar matrix in characteristic
two. This is the scalar-rigidity input for elementary central-kernel control. -/
theorem split_eq_one_of_scalar (P : Parameters) (hp : P.prime = 2)
    (g : SplitGroup P) (c : ExtensionField P) (h : g.val.val = c • 1) : g = 1 := by
  have hc := split_scalar_eq_one P hp g c h
  apply Subtype.ext
  apply Units.ext
  simpa [hc] using h

end
end Triality.Standard.ElementaryCentralKernel
