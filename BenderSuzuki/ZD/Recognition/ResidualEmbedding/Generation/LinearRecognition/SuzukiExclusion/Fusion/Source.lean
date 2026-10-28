module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.SylowStructure
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.ZStarDescent
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.LocalRecognition.Source
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting

/-!
# The final Suzuki fusion contradiction

The local and counting source theorems give the original nondistinguished
involution fusion. The established Sylow and weak-closure arguments then
produce an order-two factor in the literal quotient M/A. Z-star supplies a
torus-invariant Sylow subgroup at the primitive prime, contradicting the
earlier torus obstruction for the very same ambient subgroup image.

Only the authorized local geometry, semiregularity and centralizer embedding
remain explicit; the enclosing Suzuki exclusion constructs all three.
Source: GLS IV, Chapter 2, Lemmas 14.4–14.9 and Proposition 14.1.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

namespace SuzukiExclusion

/-- The Suzuki Sylow and fusion contradiction, with the earlier Lemma 12.11
fusion statement constructed from the original source hypotheses. -/
public theorem Context.false_of_geometry (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (hsemi : TorusSemiregular M t)
    (f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t)
    (hf : Function.Injective f) : False := by
  have hlocal := proper_residualGenerated_centralizer_local_data
    d.minimal d.reduction d.action d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M
    d.proper d.even_pair
  have hcount := proper_residualGenerated_centralizer_counting_of_local
    d.minimal d.reduction d.action d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M
    d.proper d.even_pair hlocal
  have s := d.sylowGeometry g hsemi
  obtain ⟨hU, hweak⟩ := d.U_card_eq_two_and_quotientFusion g hsemi f hf s
    hcount.nondistinguished_fusion
  obtain ⟨p, hp, hnp, _, _, _, hpD, hnot⟩ :=
    d.exists_prime_not_normalizing_sylow g hsemi
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨R, hR⟩ :=
    ZStarDescent.exists_torus_invariant_sylow d g s hU hweak p hnp hpD
  exact hnot R hR

end SuzukiExclusion

end BenderSuzuki.ZD
