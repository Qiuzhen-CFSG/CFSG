module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Max5Centralizer.Initial
public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Max5Centralizer.PairRigidity.Marking
public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Max5Centralizer.PairRigidity.Checks
public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Max5Centralizer.PairRigidity.Separation

/-!+# Two marked-pair certificates for Held's max5 core centralizer

A permutation preserving the graph and centralizing the actual embedded
core transports all seven inverse-generator colors and neighbor sums.
Individualizing the published initial weight at `(48,0)` gives a separating
color after three certified refinements, so its pointwise stabilizer is
trivial. Jointly individualizing `(48,0)` and `(334,990)`, with the same
decoder on both copies, gives unequal color counts after two refinements.
Thus no such permutation sends the first ordered pair to the second.

Every marking, refinement, count and separation equation is checked by
Lean's kernel against the original graph and actual core action. Neither
conclusion uses candidate-pair exhaustion, a centralizer bound, or an order
or simplicity assertion. The certificates support the intrinsic centralizer
assembly for GLS3 Table 5.3p, the Held 2B extraspecial centralizer.
-/

namespace Held.TwoLocalCandidates.Cores.Max5Centralizer

open PairRigidity.Certificate

/-- The pointwise stabilizer of `(48,0)` in the actual graph centralizer is trivial. -/
public theorem fixed_pair_eq_one (σ : Equiv.Perm (Fin 2058))
    (hσ : σ ∈ graphCentralizer) (h48 : σ 48 = 48) (h0 : σ 0 = 0) : σ = 1 := by
  have hmarked := fixed_mark_transport σ hσ h48 h0
  have h1 := decoded_transport σ hσ hmarked decode1 decode_left1 decode_left1
  have h2 := decoded_transport σ hσ h1 decode2 decode_left2 decode_left2
  have h3 := decoded_transport σ hσ h2 decode3 decode_left3 decode_left3
  exact eq_one_of_separating σ h3 decodeVertex separating

/-- No element of the actual graph centralizer sends `(48,0)` to `(334,990)`. -/
public theorem exceptional_pair_impossible (σ : Equiv.Perm (Fin 2058))
    (hσ : σ ∈ graphCentralizer) (h48 : σ 48 = 334) (h0 : σ 0 = 990) : False := by
  have hmarked := exceptional_mark_transport σ hσ h48 h0
  have h1 := decoded_transport σ hσ hmarked decode1 decode_left1 decode_right1
  have h2 := decoded_transport σ hσ h1 decode2 decode_left2 decode_right2
  exact counts_ne (colorCount_transport σ h2 4906631)

end Held.TwoLocalCandidates.Cores.Max5Centralizer
