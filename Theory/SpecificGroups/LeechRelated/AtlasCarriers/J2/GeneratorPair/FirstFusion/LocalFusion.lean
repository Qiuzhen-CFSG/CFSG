module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion.LocalData
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion.LocalFusion.Soundness

/-!+# Enumeration and involution fusion in the concrete J₂ centralizer

The 1920 published words cover the centralizer of `t = (abab⁻¹)⁶`.
Every nonidentity involution among them is conjugate to `a` or `t`, with a
conjugator in the actual degree-100 carrier. These are the two finite local
inputs to `first_generator_conjugate_of_finite_checks` in `Reduction`.

The proof checks the word tree, generator transitions, Schreier factors,
and explicit conjugating words in the kernel. It does not require the order
or simplicity of J₂. Source: retained ATLAS `J2G1-p100B0`; GLS3, Table 5.3g.
-/

public section
namespace Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion

theorem centralizerElement_cover :
    ∀ z ∈ centralizer, ∃ i : Fin 1920, z = centralizerElement i :=
  LocalCertificate.cover

theorem centralizerElement_involution_fusion :
    ∀ i : Fin 1920, centralizerElement i ^ 2 = 1 → centralizerElement i ≠ 1 →
      IsConj a (centralizerElement i) ∨ IsConj t (centralizerElement i) := by
  intro i hsq hne
  have h := LocalCertificate.fusion i hsq hne
  by_cases hi : LocalCertificate.fusionA i = true
  · exact Or.inl (by simpa [LocalCertificate.base, hi] using h)
  · exact Or.inr (by simpa [LocalCertificate.base, hi] using h)

end Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion
