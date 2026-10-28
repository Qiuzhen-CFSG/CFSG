module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.SylowStructure.Factorization
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.SylowStructure.TwoLocalContract
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.SylowStructure.TwoLocal.Foundations
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.SylowStructure.TwoLocal.Translation
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.SylowStructure.TwoLocal.Endgame

/-!
# The two-local Suzuki argument

This module proves all conclusions of GLS4, Chapter 2, Lemma 14.6 from the
original context, local geometry and torus semiregularity. No further
centralizer embedding is needed once that geometry is supplied.

Write A = closure (Z ∩ M). The translation argument constructs the actual
quotient S/T ≃ A from an S-invariant coset Au, establishing the needed torus
normalization before using its regular action. The endgame then proves
ambient Sylow maximality, relative normality, Z(S) = A, [S,U] ≤ A, the
normalizer product and the full S-conjugation orbits on every Au.

The assembly below discharges the endgame's quotient premise and preserves
the literal quotient and direct-conjugation conventions of the contract.
Source: GLS4, Chapter 2, Lemma 14.6, `refs/KGroup/GLS4/Chapter2.tex`.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

/-- GLS4, Chapter 2, Lemma 14.6, with the translation quotient constructed
from the original conditional inputs. -/
public theorem Context.twoLocalSylowGeometry (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (hsemi : TorusSemiregular M t) :
    TwoLocalSylowGeometry g :=
  d.twoLocalSylowGeometry_of_quotient g hsemi (d.twoLocal_quotient_equiv g hsemi)

end BenderSuzuki.ZD.SuzukiExclusion
