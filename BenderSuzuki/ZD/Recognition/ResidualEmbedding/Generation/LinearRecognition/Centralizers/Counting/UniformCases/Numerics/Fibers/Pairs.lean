module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.UniformCases.Numerics.Inputs

/-!
# The two local pair sets in Lemma 12.8

The actor fiber is counted by ordered odd-product involution pairs in its
actual distinguished centralizer closure. The distinguished fiber is counted
by displacement pairs in the elementary binary subgroup and the actor's
ambient conjugacy class inside M. These sets retain the quotient-free source
conventions and do not contain numerical or recognition assumptions.
Source: GLS4, Chapter 2, proof of Lemma 12.8, `refs/KGroup/GLS4/Chapter2.tex`.
-/

namespace BenderSuzuki.ZD
open Subgroup
universe u
variable {G : Type u} [Group G]

/-- Ordered local involution pairs, including equal factors. -/
@[expose] public def ResidualCentralizerOddPairs (Z : Set G) (v : G) : Type u :=
  {p : centralizerClosure Z v × centralizerClosure Z v //
    orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ Odd (orderOf (p.1 * p.2))}

/-- The literal displacement by an M-element in the ambient actor class.
The first factor may range over all of A: the equation with nonidentity z
excludes the identity automatically. -/
@[expose] public def ResidualDistinguishedDisplacementPairs
    (Z : Set G) (M : Subgroup G) (z v : G) : Type u :=
  {p : closure (Z ∩ (M : Set G)) × M // IsConj v (p.2 : G) ∧
    (p.1 : G)⁻¹ * ((p.2 : G) * (p.1 : G) * (p.2 : G)⁻¹) = z}

end BenderSuzuki.ZD
