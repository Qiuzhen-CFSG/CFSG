module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.GeometryContract
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Regularity.OddNormalizer
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Regularity.Action
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Regularity.TorusFixedPoints
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Regularity.PrimeStabilizers

/-!
# Torus semiregularity and the regular action

Lemma 12.12 and its application (12F) are proved in `OddNormalizer`;
`TorusFixedPoints` completes Proposition 12.13, including the Sylow
fixed-intersection and weak-closure arguments. Every nonidentity element
of the actual torus therefore fixes exactly the two distinguished cosets.

This discharges the remaining premise of the prime-stabilizer argument.
The resulting free action of `L` on the literal cosets moved by any
involution of `D` is regular, since the moved set has cardinality `|L|`.
The centralizer acts faithfully on that set and commutes with `L`, so
inverse evaluation gives an injective homomorphism `C_G(L) →* L`.
The inverse accounts for the opposite-group convention. Evenness of `D`
supplies the involution needed for this final construction.

Source: `refs/KGroup/GLS4/Chapter2.tex`, Lemmas 12.12–12.14.
-/

namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup

universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ} (d : Context Z M z t m)
include d

/-- Every stabilizer in `L` of a coset moved by a pair-stabilizer involution
is trivial; Proposition 12.13 supplies the torus premise. -/
public theorem Context.movedPoint_free {u : G}
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (x : residualGenerated M z t) (beta : G ⧸ M)
    (hbeta : u • beta ≠ beta) (hfix : (x : G) • beta = beta) : x = 1 :=
  d.movedPoint_free_of_torus_semiregular d.torus_semiregular huD hu x beta hbeta hfix

/-- Lemma 12.14(a): `L` acts regularly on the literal cosets moved by any
involution in `D`, with no additional freeness or fixed-point premise. -/
public theorem Context.regular_on_moved {u : G}
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    {a b : G ⧸ M} (ha : u • a ≠ a) (hb : u • b ≠ b) :
    ∃! x : residualGenerated M z t, (x : G) • a = b :=
  d.regular_on_moved_of_free huD hu (d.movedPoint_free huD hu) ha hb

/-- Lemma 12.14(b): the actual centralizer embeds in `L`. An involution is
selected from the even pair stabilizer, and inverse evaluation of its
regular moved-coset action produces the homomorphism into `L`. -/
public theorem Context.centralizer_embedding :
    ∃ f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t,
      Function.Injective f := by
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card'
    (G := residualPairStabilizer M t) 2 d.even_pair.two_dvd
  have hui : PFAppendixIII.IsInvolution (u : G) := IsInvolution.map_of_injective
    (orderOf_eq_prime_iff.mp hu).symm (residualPairStabilizer M t).subtype
    Subtype.val_injective
  exact d.centralizer_embedding_of_regular u.property hui
    (fun _ _ ha hb => d.regular_on_moved u.property hui ha hb)

end BenderSuzuki.ZD.SuzukiExclusion
