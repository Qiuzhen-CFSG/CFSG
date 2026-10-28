module

public import Stellmacher.Recognition.Parrott.NormalizerRootOrbitCensus
public import Stellmacher.Recognition.Parrott.NormalizerTransportRootCoordinates

/-!
# Root-fiber normalization on the supplied Parrott frame

The imported root census counts sixteen roots in the normalizer core and
eight in each of the two elementary cosets. The coordinate theorem places
the transported x in caw⟨u,t,z⟩ and the transported a in u⟨z⟩. The explicit
involution twists remove the root discrepancy up to tz. Applying the
coordinate theorem again to the replacement transport recovers its a-image,
so both required alternatives hold for one and the same involution.

This completes normalization without an additional involution-orbit census
premise. The original elementary subgroup, fusion data and centralizer frame
are retained literally; only the transport involution is replaced.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.682, the root-coordinate and sixteen-root paragraphs.
-/

namespace Stellmacher.Recognition.ParrottNormalizerTransportData

variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}
variable {f : ParrottCentralizerGeneratorData n}

/-- Replace any supplied transport by an involution with both required image
alternatives, preserving the supplied frame and all transport fields. -/
public theorem exists_normalized (k : ParrottNormalizerTransportData f)
    (h : ParrottCentralizerHypotheses z) :
    ∃ k' : ParrottNormalizerTransportData f,
      (k'.s⁻¹ * f.a * k'.s = f.u ∨ k'.s⁻¹ * f.a * k'.s = f.u * z) ∧
      (k'.s⁻¹ * f.x * k'.s = f.c * f.a * f.w ∨
        k'.s⁻¹ * f.x * k'.s = f.c * f.a * f.w * n.t * z) := by
  obtain ⟨ha, hx⟩ := k.root_coordinates h
  obtain ⟨k', hk'⟩ := k.exists_corrected_of_local_coordinates ha hx
  exact ⟨k', k'.a_conj_eq_u_or_uz h, hk'⟩

/-- Package root-fiber normalization as a seed on the literal supplied frame.
The transport-existence construction can apply this to any of its witnesses. -/
public theorem exists_seed (k : ParrottNormalizerTransportData f)
    (h : ParrottCentralizerHypotheses z) : Nonempty (ParrottNormalizerSeedData f) := by
  obtain ⟨k', ha, hx⟩ := k.exists_normalized h
  exact ⟨k'.toSeed ha hx⟩

end Stellmacher.Recognition.ParrottNormalizerTransportData
