module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ActionClassification.S3Normalization.CubicCertificate
/-!
# Normalizing a nontrivial cubic binary automorphism

A nonidentity order-three automorphism with a nonidentity fixed vector has
an actual multiplicative basis in which it cycles the first three coordinate
vectors. The binary-matrix certificate constructs the fixed and moving planes;
faithful encoding transfers its kernel and intertwining checks to the given
automorphism. This provides the cubic step for the labelled S₃ reduction
supporting Huppert–Blackburn, *Finite Groups III*, XII.1.18(b), p.314.
-/

open Theory.GroupTheory.HeldM22A10.LocalModelDichotomy
open Theory.GroupTheory.HeldM22A10.NonsplitAlternatives
open Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification
open Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification.S3Normalization
open Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification.S3Normalization.BinaryMatrices
namespace Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification.S3Normalization

/-- The basis is oriented from the standard model to the given operator. -/
public theorem normalize_cubic (t : MulAut BinaryFour) (hcube : t ^ 3 = 1) (hne : t ≠ 1)
    (hfixed : ∃ v : BinaryFour, v ≠ 1 ∧ t v = v) :
    ∃ f : MulAut BinaryFour, ∀ v, t (f v) = f (permutationAction threeCycle v) := by
  let m := ofAut t
  have hm : comp m (comp m m) = ident := by
    rw [← ofAut_mul, ← ofAut_mul, ← ofAut_one]
    apply congrArg ofAut
    simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using hcube
  have hn : m ≠ ident := by
    intro h
    apply hne
    apply ofAut_injective
    exact h.trans ofAut_one.symm
  obtain ⟨v, hv, htv⟩ := hfixed
  have hf : ∃ w : Code, w ≠ 0 ∧ app m w = w := by
    refine ⟨encode v, ?_, ?_⟩
    · intro he
      apply hv
      rw [← decode_encode v, he, decode_zero]
    · apply decode_injective
      rw [← lin_decode, decode_encode, lin_ofAut]
      exact htv
  obtain ⟨hk, hi⟩ := cubic_certificate m.1 m.2.1 m.2.2.1 m.2.2.2 hm hn hf
  refine ⟨aut _ hk, ?_⟩
  have he := congrArg lin hi
  rw [lin_comp, lin_comp, lin_ofAut, lin_cubic] at he
  intro v
  exact congrArg (fun h : BinaryFour →* BinaryFour => h v) he
end Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification.S3Normalization
