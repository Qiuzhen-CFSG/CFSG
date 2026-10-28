module

public import Theory.SpecificGroups.PSL3.OuterSolvable.StandardQuotient
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Commutator generation removes field automorphisms in PSL₃

The quotient of the actual outer automorphism group by its diagonal image
is abelian. Consequently the image of D = [D,T] under any homomorphism to
Aut(PSL₃) is inner-diagonal. This works on the full faithful action and does
not identify a nonsplit extension with a split one. Standard-automorphism
coverage is the sole model theorem retained as an explicit earlier input.

Source: GLS3, Theorem 2.5.12; Aschbacher–Smith, the residual identity and
extension alternatives in the proof of 13.6.6, printed p.927.
-/

public section
open scoped MatrixGroups IsMulCommutative
open Subgroup
open Matrix.PSL3.OuterSolvable
namespace Matrix.PSL3.NormalizedRootCentralizers
variable {F : Type*} [Field F] [Finite F]

theorem commutator_generated_innerDiagonal {H : Type*} [Group H]
    (f : H →* MulAut PSL(3,F)) (D T : Subgroup H) (hD : ⁅D, T⁆ = D)
    (hcover : standard F = ⊤) : D.map f ≤ innerDiagonal F := by
  let N := innerDiagonalOuter F
  let : N.Normal := innerDiagonalOuter_normal_of_coverage F hcover
  let : IsMulCommutative (MulAut.Outer PSL(3,F) ⧸ N) :=
    outerDiagonalQuotient_isMulCommutative_of_coverage F hcover
  let q := QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))
  let g := (QuotientGroup.mk' N).comp (q.comp f)
  have hg : D.map g = ⊥ := by
    rw [← hD, map_commutator]
    exact commutator_eq_bot_iff_le_centralizer.mpr fun _ _ =>
      mem_centralizer_iff.mpr fun _ _ => mul_comm _ _
  rintro _ ⟨d, hd, rfl⟩
  have hdg : g d = 1 := by
    have hh := mem_map_of_mem g hd
    rwa [hg, mem_bot] at hh
  have hdq : q (f d) ∈ innerDiagonalOuter F := (QuotientGroup.eq_one_iff _).mp hdg
  have he : (innerDiagonalOuter F).comap q = innerDiagonal F := by
    rw [← innerDiagonal_map_outer, comap_map_eq, QuotientGroup.ker_mk']
    exact sup_eq_left.mpr (inner_le_innerDiagonal F)
  exact he ▸ hdq

end Matrix.PSL3.NormalizedRootCentralizers
