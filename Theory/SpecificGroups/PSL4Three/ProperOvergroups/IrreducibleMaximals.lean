module

public import Theory.SpecificGroups.PSL4Three.ProperOvergroups.IrreducibleMaximals.Symplectic

/-!
# Irreducible maximal subgroups of PSL₄(3): remaining assembly

The symplectic similitude case has small layers by the actual matrix and
quotient construction in `Symplectic`. Two other concrete matrix candidates
are specified in `Data`.

The theorem below records the remaining assembly with its premises explicit.
Exhaustive intrinsic coverage and the two candidate layer constructions are
still required. In particular the candidate definitions, or a successful build
of this conditional theorem, do not establish a maximal-subgroup classification.

Source application: Aschbacher–Smith, Theorem 0.1.2(4) and condition K,
printed pp.4 and 482 of `refs/quasithin.pdf`.
-/

namespace Matrix.PSL4Three.ProperOvergroups.IrreducibleMaximals

/-- Assemble the irreducible case once exhaustive coverage and the remaining
concrete layer calculations have been proved. -/
public theorem irreducible_maximal_hasSmallLayers_of_coverage
    (hcoverage : ∀ M : Subgroup PSL, IsCoatom M → ¬ Reducible M →
      ¬ Group.IsSolvable M → SymplecticSimilitudes M ∨
        ∃ i : Fin 2, ∃ g : PSL, M = (candidate i).map (MulAut.conj g).toMonoidHom)
    (hcandidates : ∀ (i : Fin 2) (g : PSL),
      HasSmallLayers ((candidate i).map (MulAut.conj g).toMonoidHom))
    (M : Subgroup PSL) (hM : IsCoatom M) (hirr : ¬ Reducible M)
    (hnsolv : ¬ Group.IsSolvable M) : HasSmallLayers M := by
  rcases hcoverage M hM hirr hnsolv with hsymp | ⟨i, g, rfl⟩
  · exact hasSmallLayers_of_symplecticSimilitudes M hsymp
  · exact hcandidates i g

end Matrix.PSL4Three.ProperOvergroups.IrreducibleMaximals
