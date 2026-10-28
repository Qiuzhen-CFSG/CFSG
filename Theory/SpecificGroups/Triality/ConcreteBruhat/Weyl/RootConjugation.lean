module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.Weyl.Basic
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Weyl.RootConjugation.RootCurves
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Weyl.RootConjugation.Torus

/-!
# All-root Weyl conjugation and normalization of the split torus

`RootConjugation.weylWord_rootCurveUnit_conjugation` proves that the actual
simple Weyl word conjugates every canonical integral Geck root curve to its
reflected curve with the same parameter. Negative roots use their actual
negative-simple Tits routes; reduction modulo two removes integral signs.

`RootConjugation.weylWord_torusWord_conjugation` gives the Cartan reflection
formula on the four original simple-coroot words. Closure then shows that the
whole published split Weyl subgroup normalizes the original word-generated
torus. Both results hold for every characteristic-two parameter, including
q = 2. No matrix/root Weyl equivalence is assumed.

Source: the concrete split-group ingredients for GLS3 2.3.8(b) and 2.4.8(e,f)
(`refs/KGroup/GLS3/chapter2.tex`). This module does not assert the remaining
Bruhat or twisted fixed-point conclusions of 2.3.8.
-/

@[expose] public section
namespace Triality.Standard.ConcreteBruhat
noncomputable section

/-- The actual split Weyl subgroup normalizes the original coroot-word torus. -/
theorem splitWeylSubgroup_le_normalizer_splitTorus (P : Parameters) (hp : P.prime = 2) :
    splitWeylSubgroup P ≤ Subgroup.normalizer (splitTorus P) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  exact RootConjugation.weylWord_mem_normalizer_splitTorus P hp i

end
end Triality.Standard.ConcreteBruhat
