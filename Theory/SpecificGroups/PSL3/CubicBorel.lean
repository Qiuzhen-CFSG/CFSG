module

public import Theory.SpecificGroups.PSL3.CubicBorel.Reduction
public import Theory.SpecificGroups.PSL3.CubicBorel.Roots
public import Theory.SpecificGroups.PSL3.CubicBorel.Torus

/-!
# Cubic generation in a specified PSL₃ Borel

The positive root groups belong to the closure of the order-three elements
of the Borel. The reduction conjugates the specified Sylow and both given
matrices into standard coordinates and transports the result back.
The triangular torus comparison cancels the normalized determinant using
a power of the supplied outer actor. Combining the two calculations proves
generation for all cubic linear actors, including the identity, with the
original Sylow subgroup and the original outer actor retained.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), final paragraph
of 15.3.37, printed p.1135, and A.3.18, printed pp.52--53.
-/

public section

open scoped MatrixGroups
open Subgroup Matrix.PSL3.OuterSolvable
namespace Matrix.PSL3.CubicBorel
variable (F : Type*) [Field F] [Finite F]

/-- Cubic Borel generation conditional only on the triangular torus calculation.
Both original matrices and the original Sylow subgroup occur in the conclusion. -/
theorem generation_of_triangularComparison {n : ℕ} (hn : 0 < n) (he : Even n)
    (hF : Nat.card F = 2 ^ n) (hcompare : TriangularCubicComparison F)
    (T : Sylow 2 PSL(3,F)) (d₀ g : GL (Fin 3) F)
    (hout : linearConj F d₀ ∉ MulAut.innerSubgroup PSL(3,F))
    (hd : linearConj F d₀ ^ 3 = 1)
    (hdT : (T : Subgroup PSL(3,F)).map (linearConj F d₀).toMonoidHom = T)
    (hg : linearConj F g ^ 3 = 1)
    (hgT : (T : Subgroup PSL(3,F)).map (linearConj F g).toMonoidHom = T) :
    linearConj F g ∈
      (closure {z | z ∈ normalizer (T : Set PSL(3,F)) ∧ orderOf z = 3}).map MulAut.conj ⊔
        zpowers (linearConj F d₀) :=
  generation_of_calculations F hn hF (unipotent_le_cubicClosure F he hF)
    hcompare T d₀ g hout hd hdT hg hgT

/-- Every cubic linear actor preserving the specified Sylow lies in the join
of its cubic Borel inner actions with the supplied outer cubic actor. -/
theorem generation {n : ℕ} (hn : 0 < n) (he : Even n) (hF : Nat.card F = 2 ^ n)
    (T : Sylow 2 PSL(3,F)) (d₀ g : GL (Fin 3) F)
    (hout : linearConj F d₀ ∉ MulAut.innerSubgroup PSL(3,F))
    (hd : linearConj F d₀ ^ 3 = 1)
    (hdT : (T : Subgroup PSL(3,F)).map (linearConj F d₀).toMonoidHom = T)
    (hg : linearConj F g ^ 3 = 1)
    (hgT : (T : Subgroup PSL(3,F)).map (linearConj F g).toMonoidHom = T) :
    linearConj F g ∈
      (closure {z | z ∈ normalizer (T : Set PSL(3,F)) ∧ orderOf z = 3}).map MulAut.conj ⊔
        zpowers (linearConj F d₀) :=
  generation_of_triangularComparison F hn he hF (triangularCubicComparison F)
    T d₀ g hout hd hdT hg hgT

end Matrix.PSL3.CubicBorel
