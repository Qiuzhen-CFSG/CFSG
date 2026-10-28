module

public import Theory.SpecificGroups.PSp4Three.IrreducibleOvergroups.Reduction
public import Theory.SpecificGroups.PSp4Three.IrreducibleOvergroups.TrivialTwoCore.QuadraticNormalizer

/-!+# The trivial-two-core branch: quadratic extension reduction

The explicit quadratic normalizer in the imported module is a proper subgroup
of the actual projective symplectic group. If each maximal irreducible
nonsolvable subgroup with trivial two-core lies in a conjugate of that
normalizer, a faithful six-point action of the normalizer restricts and
transports to the required action of the subgroup.

Both premises remain independent mathematical obligations: exhaustive
quadratic-structure coverage, and construction of the normalizer's action.
This conditional reduction does not establish the unconditional branch.

Source application: Aschbacher–Smith, Theorem 0.1.2(4), condition K,
printed pp.4 and 482 of `refs/quasithin.pdf`.
-/

namespace Matrix.PSp4Three

/-- Conditional assembly using an actual quadratic extension normalizer.
Both the coverage theorem and the model action must still be supplied. -/
public theorem exists_faithful_sixPointAction_of_quadraticNormalizer_coverage
    (hcoverage : ∀ M : Subgroup (PSp 2 (ZMod 3)), IsCoatom M →
      ¬ HasInvariantSubspace M → ¬ Group.IsSolvable M → pCore 2 M = ⊥ →
      ∃ g : PSp 2 (ZMod 3),
        M ≤ TrivialTwoCore.projectiveQuadraticNormalizer.map (MulAut.conj g).toMonoidHom)
    (haction : ∃ f : TrivialTwoCore.projectiveQuadraticNormalizer →*
      Equiv.Perm (Fin 6), Function.Injective f)
    (M : Subgroup (PSp 2 (ZMod 3))) (hmax : IsCoatom M)
    (hirr : ¬ HasInvariantSubspace M) (hnsol : ¬ Group.IsSolvable M)
    (hcore : pCore 2 M = ⊥) :
    ∃ f : M →* Equiv.Perm (Fin 6), Function.Injective f :=
  TrivialTwoCore.exists_faithful_sixPointAction_of_conjugate haction M
    (hcoverage M hmax hirr hnsol hcore)

end Matrix.PSp4Three
