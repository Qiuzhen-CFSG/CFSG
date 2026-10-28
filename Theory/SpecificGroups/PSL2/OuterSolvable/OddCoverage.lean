module

public import Theory.SpecificGroups.PSL2.OuterSolvable.OddCoverage.Multiplicativity
public import Theory.SpecificGroups.PSL2.OuterSolvable.OddCoverage.Normalization

/-!
# Inner–diagonal–field coverage for odd PSL₂

Inner and diagonal normalization, followed by recovery of field multiplication
on the upper root group, gives the inner–diagonal–field factorization of an
automorphism. The reconstruction uses the actual center quotient and entrywise
field action, so it requires no lift of an abstract PSL₂ automorphism to SL₂.

Both steps are proved in the imported modules. This supplies the coverage
assertion in the A₁ case of GLS3, Theorem 2.5.12 and §2.7
(`refs/KGroup/GLS3/chapter2.tex`, lines 854 and 1109–1115). Fixing `upper 1`
removes the sign ambiguity left by fixing the projective Weyl element.
The proof works on arbitrary finite-field carriers and includes cardinality
nine; no central-extension lifting theorem or automorphism hypothesis is used.
-/

namespace Theory.PSL2.OuterSolvable.OddCoverage

variable {K : Type*} [Field K]

/-- Conditional assembly from inner–diagonal normalization and multiplication
recovery. Neither premise is asserted by this theorem. -/
public theorem semilinear_coverage_of_root_reductions
    (normalize : ∀ a : MulAut (Group K),
      ∃ (g : Group K) (u : Kˣ) (b : MulAut (Group K)),
        a = MulAut.conj g * diagonalAutHom u * b ∧
        (rootGroup K).map b.toMonoidHom = rootGroup K ∧
        b (weyl K) = weyl K ∧ b (upper 1) = upper 1)
    (multiply : ∀ (b : MulAut (Group K))
      (hU : (rootGroup K).map b.toMonoidHom = rootGroup K),
      b (weyl K) = weyl K → b (upper 1) = upper 1 →
      ∀ s t : K,
        rootParameter b hU (s * t) = rootParameter b hU s * rootParameter b hU t)
    (a : MulAut (Group K)) :
    ∃ (g : Group K) (u : Kˣ) (σ : K ≃+* K),
      a = MulAut.conj g * diagonalAutHom u * projectiveFieldAutHom σ := by
  obtain ⟨g, u, b, hab, hU, hw, h1⟩ := normalize a
  obtain ⟨σ, hσ⟩ := eq_projectiveFieldAut_of_rootParameter_mul b hU hw
    (multiply b hU hw h1)
  exact ⟨g, u, σ, hσ ▸ hab⟩

end Theory.PSL2.OuterSolvable.OddCoverage

namespace Theory.PSL2.OuterSolvable

/-- Every automorphism of odd finite-field PSL₂ with more than three field
elements is inner times diagonal times the actual entrywise field action. -/
public theorem odd_semilinear_coverage {K : Type*} [Field K] [Finite K]
    (hchar : ringChar K ≠ 2) (_hcard : 3 < Nat.card K) (a : MulAut (Group K)) :
    ∃ (g : Group K) (u : Kˣ) (σ : K ≃+* K),
      a = MulAut.conj g * diagonalAutHom u * projectiveFieldAutHom σ := by
  exact OddCoverage.semilinear_coverage_of_root_reductions
    (OddCoverage.exists_root_weyl_one_normalization hchar)
    (fun b hU _ h1 => OddCoverage.rootParameter_mul hchar b hU h1) a

end Theory.PSL2.OuterSolvable
