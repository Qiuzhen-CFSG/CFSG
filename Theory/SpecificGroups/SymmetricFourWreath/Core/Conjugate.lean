module
public import Theory.SpecificGroups.SymmetricFourWreath.Core.Placement

/-!
# A marked conjugate of z in Q outside its center

The diagonal of the short reflection sr(1) lies in Q but not in its central
line. Conjugation by the diagonal transposition (2 3) carries the marked z
to this element in the original S4 wreath model.

Source: Aschbacher–Smith 13.9.8(1), printed p.972 (PDF p.989).
-/

public section
namespace SymmetricFourWreath
open Subgroup
private instance : DecidableEq P := (RegularWreathProduct.equivProd D8 C2).injective.decidableEq

theorem core_conjugate_z : ∃a:P,a∈coreInP ∧ a∉centralLine ∧ IsConj z (sylowEmbedding a) := by
  let a : P := pair (DihedralGroup.sr 1,DihedralGroup.sr 1)
  refine ⟨a,?_,?_,?_⟩
  · rw [mem_coreInP]
    decide +kernel
  · rw [mem_centralLine]
    decide +kernel
  · apply isConj_iff.mpr
    let g : W := ⟨fun _=>Equiv.swap 2 3,1⟩
    refine ⟨g,?_⟩
    apply RegularWreathProduct.ext
    · funext i
      revert i
      decide +kernel
    · decide +kernel
end SymmetricFourWreath

