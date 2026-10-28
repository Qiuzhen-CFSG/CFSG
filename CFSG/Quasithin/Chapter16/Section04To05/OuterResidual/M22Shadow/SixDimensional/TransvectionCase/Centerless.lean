module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.M22Shadow.SixDimensional.TransvectionCase.Coordinates

/-!
# The centerless transvection endgame in the actual shadow

The marked transvection displacements imply [V,X] = ⟨r,z⟩. Relative
Q-normality and the centerless direct-product decomposition supply the
invariance and disjointness hypotheses in reduced commutation. The local
normalizer, acting trivially on V/Q, must therefore fix r, contrary to its
actual conjugation action.

This proves the endgame from two constructed marked elements and a trivial
two-core. Their construction from T_C > ⟨z⟩ remains a prerequisite; this
module does not claim to prove that source case by assuming those outputs.
Source: Aschbacher–Smith, proof of Lemma 16.4.7, printed p.1187.
-/

@[expose] public section

open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow.SixDimensional.TransvectionCase
open Subgroup BinaryLinear BinaryTransvectionGroups
variable {G : Type*} [Group G]
variable (L : Subgroup G) (g r z : G) [IsElementaryAbelian 2 (shadowSpace L r z)]

/-- An element acting trivially modulo the actual Q has a quotient-trivial
linear action. The premise is stated in the original group. -/
theorem linearAction_mem_quotientFixer (n : shadowOvergroup L g r z)
    (hn : ∀ v ∈ shadowSpace L r z,
      (n : G) * v * (n : G)⁻¹ * v⁻¹ ∈ residualCore L r) :
    linearAction L g r z n ∈ quotientFixer (subspace L r z (residualCore L r)) := by
  intro v
  change ((n : G) * (v.toMul : G) * (n : G)⁻¹) / (v.toMul : G) ∈ residualCore L r
  simpa only [div_eq_mul_inv] using hn v.toMul v.toMul.property

/-- The actual t and t′ supplied by the normalizer construction force
the local action to fix r. -/
theorem fixes_r_of_marked_transvections
    (hQ : shadowOvergroup L g r z ≤ normalizer (residualCore L r : Set G))
    (hcore : pCore 2 (image L g r z) = ⊥)
    (hdis : Disjoint (residualCore L r) (zpowers r ⊔ zpowers z))
    (t u : shadowOvergroup L g r z)
    (ht : linearAction L g r z t ∈ quotientFixer (centerLine (zVector L r z)))
    (hu : linearAction L g r z u ∈ quotientFixer (centerLine (rVector L r z)))
    (htr : linearAction L g r z t (rVector L r z) - rVector L r z = zVector L r z)
    (huz : linearAction L g r z u (zVector L r z) - zVector L r z = rVector L r z)
    (htQ : ∀ q ∈ residualCore L r, (t : G) * q = q * (t : G))
    (huQ : ∀ q ∈ residualCore L r, (u : G) * q = q * (u : G))
    (n : shadowOvergroup L g r z)
    (hn : ∀ v ∈ shadowSpace L r z,
      (n : G) * v * (n : G)⁻¹ * v⁻¹ ∈ residualCore L r) :
    (n : G) * r * (n : G)⁻¹ = r := by
  have htfix : linearAction L g r z t ∈ pointwiseFixer (subspace L r z (residualCore L r)) := by
    intro q hq
    apply Additive.toMul.injective
    apply Subtype.ext
    change (t : G) * (q.toMul : G) * (t : G)⁻¹ = q.toMul
    rw [htQ q.toMul hq, mul_inv_cancel_right]
  have hufix : linearAction L g r z u ∈ pointwiseFixer (subspace L r z (residualCore L r)) := by
    intro q hq
    apply Additive.toMul.injective
    apply Subtype.ext
    change (u : G) * (q.toMul : G) * (u : G)⁻¹ = q.toMul
    rw [huQ q.toMul hq, mul_inv_cancel_right]
  have hh := fixes_marked_pair_of_reduced (image L g r z)
    (subspace L r z (residualCore L r)) (image_le_parabolic L g r z _ hQ) hcore
    ((linearAction L g r z).rangeRestrict t) ((linearAction L g r z).rangeRestrict u)
    (rVector L r z) (zVector L r z) ht hu htr huz htfix hufix
    (core_disjoint_marked_plane L r z hdis)
    ((linearAction L g r z).rangeRestrict n) (linearAction_mem_quotientFixer L g r z n hn)
  exact congrArg (fun v : Space L r z => (v.toMul : G)) hh.1

/-- Conditional centerless endgame, retaining the nontrivial action on the
actual r. Construction of the transvections and two-core bound is required. -/
theorem centerless_endgame
    (hQ : shadowOvergroup L g r z ≤ normalizer (residualCore L r : Set G))
    (hcore : pCore 2 (image L g r z) = ⊥)
    (hdis : Disjoint (residualCore L r) (zpowers r ⊔ zpowers z))
    (t u : shadowOvergroup L g r z)
    (ht : linearAction L g r z t ∈ quotientFixer (centerLine (zVector L r z)))
    (hu : linearAction L g r z u ∈ quotientFixer (centerLine (rVector L r z)))
    (htr : linearAction L g r z t (rVector L r z) - rVector L r z = zVector L r z)
    (huz : linearAction L g r z u (zVector L r z) - zVector L r z = rVector L r z)
    (htQ : ∀ q ∈ residualCore L r, (t : G) * q = q * (t : G))
    (huQ : ∀ q ∈ residualCore L r, (u : G) * q = q * (u : G))
    (hn : ∃ n : shadowOvergroup L g r z,
      (∀ v ∈ shadowSpace L r z,
        (n : G) * v * (n : G)⁻¹ * v⁻¹ ∈ residualCore L r) ∧
      (n : G) * r * (n : G)⁻¹ ≠ r) : False := by
  obtain ⟨n, hn, hnr⟩ := hn
  exact hnr (fixes_r_of_marked_transvections L g r z hQ hcore hdis t u
    ht hu htr huz htQ huQ n hn)

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow.SixDimensional.TransvectionCase
