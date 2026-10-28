module

public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue
public import Theory.Mathieu.M24.LocalGeometry.EvenCandidates
public import Theory.Mathieu.M24.LocalGeometry.Defs
public import Theory.GroupTheory.SylowContainingTwoLocal

/-!
# An alternative finite catalogue route to M₂₄ condition E

The candidate local groups are actual octad stabilizers and normalizers of
the two explicitly generated elementary subgroups. The catalogue obligation
classifies normal elementary subgroups inside the fixed Sylow carrier. The
independent normalizer obligation treats the 22 listed subgroups, retaining
maximality among two-locals. Neither condition is asserted by these definitions.

Source: Aschbacher–Smith, Theorem 0.1.2(5), printed pp.3–4, and GLS3,
Table 5.3e. This catalogue route requires both obligations. The unconditional
proof in `M24Even` instead uses central involutions of the actual Sylow subgroup.
-/

@[expose] public section
namespace CFSG.Quasithin.MainConverse.M24Even
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry

/-- The concrete local families whose intrinsic cores are already controlled. -/
def IsCandidateLocal (M : Subgroup M24) : Prop :=
  (∃ O : Octad, M = octadStabilizer O) ∨ ∃ k : Fin 2, M = EvenCandidates.localGroup k

/-- Exhaustiveness of the finite list among intrinsic normal elementary subgroups. -/
def NormalElementaryCatalogue : Prop :=
  ∀ R : Subgroup SylowNormalizer.candidate, R ≠ ⊥ → R.Normal →
    IsElementaryAbelian 2 R → ∃ i : Fin 22, R = EvenCatalogue.subgroup i

/-- Only the listed normalizers that are maximal two-locals require identification. -/
def NormalizerCases : Prop :=
  ∀ i : Fin 22, IsMaximalTwoLocal (EvenCatalogue.localGroup i) →
    IsCandidateLocal (EvenCatalogue.localGroup i)

end CFSG.Quasithin.MainConverse.M24Even
