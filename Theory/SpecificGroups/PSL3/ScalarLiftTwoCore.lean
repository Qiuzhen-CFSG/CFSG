module

public import Theory.SpecificGroups.PSL3.OrdinaryCenterRecognition
public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelBound

/-!
# Scalar SL3 lifts into groups with trivial two-core

A finite quasisimple cover of PSL3(F), with |F| different from two and
trivial two-core, is a quotient of the literal SL3(F) over its original
projective marking. Ordinary fields use the proved universal projection.
At field order four, the exceptional universal kernel divides 48; comparison
with the scalar projection leaves a two-group kernel, which disappears in
the target. Thus the exceptional case needs no replacement of the marking
by an abstract central-quotient identification.

Source: Aschbacher--Smith A.2.18 and I.1.3(2),(6), printed pp.40,407.
The actual source application is the linear-three minimal-parabolic row.
-/

open Subgroup Theory.GroupTheory PerfectCentralCovering
open scoped MatrixGroups
namespace Matrix.PSL3
variable {F : Type*} [Field F] [Finite F]
variable {L : Type*} [Group L] [Finite L] [IsQuasisimple L]

public theorem exists_scalar_lift_of_twoCore_eq_bot (h2 : Nat.card F ≠ 2)
    (r : L →* PSL(3,F)) (hr : Function.Surjective r)
    (hcore : pCore 2 L = ⊥) :
    ∃ k : SL(3,F) →* L, Function.Surjective k ∧ r.comp k = projection F := by
  let g : Covering L PSL(3,F) := ⟨r,hr⟩
  by_cases h4 : Nat.card F = 4
  · let c := ExceptionalFourCover.coverOver F h4
    let a := (ExceptionalFourCover.coverOver_isUniversal F h4).lift (projectionCovering F)
    have ha : (projectionCovering F).comp a = c :=
      (ExceptionalFourCover.coverOver_isUniversal F h4).lift_fac (projectionCovering F)
    have hd : Nat.card c.toMonoidHom.ker ∣
        2 ^ 4 * Nat.card (projectionCovering F).toMonoidHom.ker := by
      rw [projectionCovering_toMonoidHom,card_projectionKernel,h4]
      change Nat.card (ExceptionalFourCover.coverOver F h4).toMonoidHom.ker ∣ 48
      rw [ExceptionalFourCover.coverOver_ker]
      exact ExceptionalFourCover.kernel_card_dvd
    obtain ⟨k,hk⟩ := (ExceptionalFourCover.coverOver_isUniversal F h4).exists_covering_of_kernel_card_dvd
      a (projectionCovering F) ha hd g hcore
    exact ⟨k.toMonoidHom,k.surjective,congrArg Covering.toMonoidHom hk⟩
  · obtain ⟨k,hk,_⟩ := UniversalProjection.existsUnique_lift_of_faithful r hr g.ker_le_center
      h2 h4 (UniversalProjection.matrixMap_injective h2 h4)
    exact ⟨k,projection_lift_surjective F r g.ker_le_center k hk,hk⟩
end Matrix.PSL3
