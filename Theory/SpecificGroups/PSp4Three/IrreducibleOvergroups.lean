module

public import Theory.SpecificGroups.PSp4Three.IrreducibleOvergroups.Extraspecial

/-!
# Irreducible overgroups in PSp₄(3): assembly of the two-core alternatives

Pass to a maximal irreducible overgroup and first remove the solvable case.
For a nonsolvable overgroup, the remaining structural obligations divide
according to its actual two-core. A nontrivial two-core is to give the
extraspecial full-preimage structure; a trivial two-core is to give a
faithful six-point action. The former's quotient construction and the
latter's alternating layers are proved in the imported extension.

Both structural classification premises below remain explicit. The
unconditional irreducible-overgroup theorem is unfinished until these
premises are proved. In particular, no ATLAS list is used as an assumption
hidden in a family name or a global K-group hypothesis.

Source application: Aschbacher–Smith, Theorem 0.1.2(4), condition K,
printed pp.4 and 482 of `refs/quasithin.pdf`. The candidate maximal shapes
are described at https://brauer.maths.qmul.ac.uk/Atlas/clas/U42/.
-/

namespace Matrix.PSp4Three

/-- Conditional assembly from two disjoint intrinsic maximal-subgroup
classification obligations. Both premises still need proofs. -/
public theorem exists_alternatingLayers_overgroup_of_twoCore_alternatives
    (hcore : ∀ M : Subgroup (PSp 2 (ZMod 3)), IsCoatom M →
      ¬ HasInvariantSubspace M → ¬ Group.IsSolvable M →
      pCore 2 M ≠ ⊥ → HasExtraspecialLiftCore M)
    (htrivial : ∀ M : Subgroup (PSp 2 (ZMod 3)), IsCoatom M →
      ¬ HasInvariantSubspace M → ¬ Group.IsSolvable M →
      pCore 2 M = ⊥ → ∃ f : M →* Equiv.Perm (Fin 6), Function.Injective f)
    (U : Subgroup (PSp 2 (ZMod 3))) (hU : U ≠ ⊤)
    (hred : ¬ HasInvariantSubspace U) :
    ∃ M : Subgroup (PSp 2 (ZMod 3)), U ≤ M ∧ HasAlternatingLayers M := by
  obtain ⟨M, hM, hUM, hirr⟩ := exists_irreducible_coatom U hU hred
  refine ⟨M, hUM, ?_⟩
  by_cases hsolv : Group.IsSolvable M
  · exact Or.inl hsolv
  by_cases htwo : pCore 2 M = ⊥
  · obtain ⟨f, hf⟩ := htrivial M hM hirr hsolv htwo
    exact hasAlternatingLayers_of_faithful_sixPointAction f hf
  · exact (hcore M hM hirr hsolv htwo).hasAlternatingLayers

end Matrix.PSp4Three
