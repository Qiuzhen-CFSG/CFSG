module

public import Theory.Representation.BinaryPermutation.FiveCoreNormalizer

/-!
# The normalizer on the five-letter natural quotient

The odd-degree core-to-natural equivalence transports the actual five-letter
core normalizer calculation to the natural quotient. Every linear normalizer,
with any induced actor automorphism, is therefore an original S₅ operator.

Source application: Aschbacher–Smith, G.6.4(3), printed p.346.
-/

public section
set_option backward.isDefEq.respectTransparency false
namespace BinaryPermutation.FiveNaturalNormalizer
open FiveCentralExtension

theorem normalizer
    (f : natural (Fin 5) ≃ₗ[ZMod 2] natural (Fin 5)) (φ : MulAut Sym)
    (hf : ∀ g v, f (naturalRepresentation (Fin 5) g v) =
      naturalRepresentation (Fin 5) (φ g) (f v)) :
    ∃ s : Sym, ∀ v, f v = naturalRepresentation (Fin 5) s v := by
  have hodd : Odd (Fintype.card (Fin 5)) := by decide
  let e := coreEquivNatural (Fin 5) hodd
  have he (g : Sym) (v : core (Fin 5)) :
      e (coreRepresentation (Fin 5) g v) = naturalRepresentation (Fin 5) g (e v) :=
    coreEquivNatural_equivariant (Fin 5) hodd g v
  let F := e.trans (f.trans e.symm)
  have hF (g : Sym) (v : core (Fin 5)) :
      F (coreRepresentation (Fin 5) g v) =
        coreRepresentation (Fin 5) (φ g) (F v) := by
    apply e.injective
    simp only [F, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rw [he, hf, he, LinearEquiv.apply_symm_apply]
  obtain ⟨s, hs⟩ := FiveCoreNormalizer.normalizer F φ hF
  refine ⟨s, fun v => ?_⟩
  have hh := congrArg e (hs (e.symm v))
  simpa only [F, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    he] using hh

end BinaryPermutation.FiveNaturalNormalizer
