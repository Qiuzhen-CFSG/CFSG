module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven.Degree.Inputs
public import Theory.Representation.AbsolutelyIrreducible

/-!
# Concrete construction inputs for the binary A₇ spectrum

The characteristic-two table supplies two families: two inequivalent
four-spaces and a six-space, and the nontrivial principal-block degrees
fourteen and twenty. Here the obligations ask for actual representations
over F₂ and proofs of their absolute irreducibility. They assert neither
exhaustivity nor a bound on an arbitrary representation. Block membership
is unnecessary for the degree argument and is not part of the contracts.

The assembly uses the six candidates, including the trivial representation,
to saturate the odd-order conjugacy-class bound and then descends a simple
constituent. Absolute irreducibility of the representation being classified
is not assumed. The degree-twenty model is needed to exhaust the class bound,
even though twenty lies outside the requested degree window.

Source: Aschbacher–Smith, K.1.2, printed p.452/PDF p.463, citing GM02
Theorem 6.2 and Table 6.3; the RWTH characteristic-two decomposition matrix
of A₇ gives degrees 1, 4, 4, 6, 14, 20. That table is supporting source data,
not a proof of any construction obligation below.
-/

@[expose] public section

open Representation
namespace CFSG.Quasithin.ChapterK.Alternating.SevenSmallSpectrum

/-- Construct the two four-spaces and the six-space over the base field,
including absolute irreducibility and inequivalence of the four-spaces. -/
def SmallModelsExist : Prop :=
  ∃ (ρ₄ : Fin 2 → Representation (ZMod 2) (alternatingGroup (Fin 7))
        (Fin 4 → ZMod 2))
    (ρ₆ : Representation (ZMod 2) (alternatingGroup (Fin 7)) (Fin 6 → ZMod 2)),
    (∀ i, IsAbsolutelyIrreducible (ρ₄ i)) ∧ IsAbsolutelyIrreducible ρ₆ ∧
      Pairwise fun i j => IsEmpty ((ρ₄ i).Equiv (ρ₄ j))

/-- Construct the fourteen- and twenty-dimensional candidates over F₂ and
prove absolute irreducibility. No decomposition-matrix hypothesis is allowed. -/
def LargeModelsExist : Prop :=
  ∃ (ρ₁₄ : Representation (ZMod 2) (alternatingGroup (Fin 7)) (Fin 14 → ZMod 2))
    (ρ₂₀ : Representation (ZMod 2) (alternatingGroup (Fin 7)) (Fin 20 → ZMod 2)),
    IsAbsolutelyIrreducible ρ₁₄ ∧ IsAbsolutelyIrreducible ρ₂₀

end CFSG.Quasithin.ChapterK.Alternating.SevenSmallSpectrum
