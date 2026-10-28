module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.Words
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.NormalGeneration

/-!
# Simplicity reduction for the O'Nan projective matrix group

The eight explicit words in `Words.lean` reduce the final normal-subgroup
argument to two independent certificates: prime-order cyclic coverage and
normal generation. Cauchy's theorem supplies a prime-order element in every
nontrivial normal subgroup; conjugate-power coverage then puts a normally
generating representative in that subgroup.

The first representative already normally generates, by the kernel-checked
relations of the actual matrices. Coverage and normal generation for the
other representatives remain separate obligations. This module does not
identify a group from its order or assume the ATLAS words are a presentation.
-/

namespace ONan

/-- Once the concrete representative certificates are supplied, the model is simple. -/
public theorem isSimpleGroup_of_prime_coverage
    (hcover : ∀ x : Model, (orderOf x).Prime →
      ∃ i k g, Simplicity.primeRepresentative i = g * x ^ k * g⁻¹)
    (hgenerate : ∀ i, Subgroup.normalClosure
      ({Simplicity.primeRepresentative i} : Set Model) = ⊤) :
    IsSimpleGroup Model :=
  simple_of_prime_representatives _ hcover hgenerate

/-- Normal generation is already certified for the first representative. -/
public theorem normalClosure_primeRepresentative_zero :
    Subgroup.normalClosure ({Simplicity.primeRepresentative 0} : Set Model) = ⊤ :=
  normalClosure_generatorA_eq_top

end ONan
