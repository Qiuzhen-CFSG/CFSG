module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.LocalGeometry.Borel
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.LocalGeometry.Outer
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.LocalGeometry.Solvability
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.LocalGeometry.Stages
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.LocalGeometry.EvenNormalizer
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.LocalGeometry.OddNormalizers
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.LocalGeometry.SylowConstruction
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.LocalGeometry.CentralizerConjugacy

/-!
# Construction of the Suzuki local geometry

The marked Borel gives P its order, center and square-one set. The actual
outer action bounds the pair-stabilizer order and places the odd-quotient
residual of N_G(L), and its two-subgroups, in LJ. Recognition of the
distinguished closure in N_G(Y) gives normalizer control for every
nontrivial subgroup Y of J. The Sylow construction then supplies the
actual ambient subgroups T = PU and T < S ≤ M. The conjugate-factor
argument makes U elementary abelian, after which the embedding J → L
gives the remaining centralizer equality and solvability of J.

This assembles GLS4, Chapter 2, Lemmas 14.2–14.3 and (14A)–(14C),
`refs/KGroup/GLS4/Chapter2.tex`. The only input beyond `Context` is the
injective centralizer homomorphism authorized by Lemma 12.14(b). Its
construction remains with the regularity argument and the final Suzuki
exclusion assembly. Every field of `LocalGeometry`, including the
intermediate `SylowConfiguration`, is constructed here.
-/

namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup

universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

/-- The complete local geometry of GLS4, Chapter 2, Lemmas 14.2–14.3,
from the source context and the embedding supplied by Lemma 12.14(b). -/
public theorem Context.localGeometry (d : Context Z M z t m)
    (f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t)
    (hf : Function.Injective f) : Nonempty (LocalGeometry Z M z t m) := by
  obtain ⟨c⟩ := d.sylowConfiguration
  have hcontrol := d.normalizer_control_of_le_centralizer
  obtain ⟨hcentralizer, hUcentralizer, hUelementary⟩ :=
    d.centralizer_conjugacy f hf c hcontrol
  exact ⟨{
    T := c.T
    U := c.U
    S := c.S
    normalizer_control := hcontrol
    pair_card_dvd := d.pair_card_dvd f hf
    T_sylow := c.T_sylow
    S_sylow := c.S_sylow
    U_eq := c.U_eq
    U_sylow_pair := c.U_sylow_pair
    U_sylow_centralizer := c.U_sylow_centralizer
    P_eq := c.P_eq
    T_product := c.T_product
    P_disjoint_U := c.P_disjoint_U
    T_lt_S := c.T_lt_S
    S_le_M := c.S_le_M
    P_card := d.borelTwoCore_card
    P_center := d.borelTwoCore_center
    P_involutions := d.borelTwoCore_square_one
    centralizer_in_normalizer := hcentralizer
    centralizer_U := hUcentralizer
    U_elementary := hUelementary
    centralizer_solvable := d.centralizer_solvable_of_elementary_sylow f hf
      c.U hUelementary c.U_sylow_centralizer }⟩

end BenderSuzuki.ZD.SuzukiExclusion
