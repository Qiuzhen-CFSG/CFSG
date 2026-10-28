module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.LocalWords
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairPresentation.Completion
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairPresentation.RootPlanes

/-!
# Conditional assembly of the F4 two-node presentation

This combines two independent source steps. The all-root normal-form theorem
puts every identity word in the normal closure of the root-plane relations.
Curtis--Tits transport constructs coherent all-root elements in the two-node
completion and preserves every plane relation. Applying transport to a
simple-root identity word then makes its class trivial in that completion.

The conclusion is the original literal kernel equality consumed by
`descendOfPairPresentation` and `ofPairActions`; the companion `ActionDescent`
module applies it to those consumers. Both substantive source steps remain
explicit. This module does not assert the unconditional presentation.
Sources: GLS3 §2.9.3 (`refs/KGroup/GLS3/chapter2.tex`) and Steinberg §3,
Theorem 8 (`refs/KGroup/GLS3/Chapter2St1.tex`).
-/

public section

namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
open Theory.AlgebraicGroup.StandardRootSystem

variable (F : Type*) [Field F]

/-- The Curtis--Tits transport and the all-root normal-form theorem together
give precisely the original kernel equality. Both source obligations remain
explicit in this conditional assembly. -/
theorem ker_eq_pairRelationSubgroup_of_root_planes
    (hroot : (rootEvaluation F).ker ≤ rootPlaneRelationSubgroup F)
    (ψ : RootWord F →* PairCompletion F)
    (hsimple : ∀ (s : Bool) (i : Fin 4) (t : F),
      ψ (FreeGroup.of (signedRoot s i, t)) =
        pairQuotient F (FreeGroup.of (s, i, t)))
    (hplanes : ∀ (a b : typeF4Roots) (v : RootPlaneWord F a b),
      rootPlaneEvaluation F a b v = 1 → ψ (rootPlaneInclusion F a b v) = 1) :
    (coverEvaluation F).ker = pairRelationSubgroup F := by
  have hmark : ψ.comp (simpleRootInclusion F) = pairQuotient F := by
    apply FreeGroup.ext_hom
    rintro ⟨s, i, t⟩
    simpa only [MonoidHom.comp_apply, simpleRootInclusion_of] using hsimple s i t
  apply le_antisymm _ (pairRelationSubgroup_le F)
  intro w hw
  apply (pairQuotient_eq_one_iff F w).mp
  have hrel : simpleRootInclusion F w ∈ rootPlaneRelationSubgroup F := by
    apply hroot
    change rootEvaluation F (simpleRootInclusion F w) = 1
    rw [rootEvaluation_simpleRootInclusion]
    exact hw
  have hkill := kills_rootPlaneRelators F ψ hplanes hrel
  change ψ (simpleRootInclusion F w) = 1 at hkill
  rw [← MonoidHom.comp_apply, hmark] at hkill
  exact hkill

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
