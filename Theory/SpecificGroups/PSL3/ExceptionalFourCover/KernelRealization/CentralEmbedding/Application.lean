module

public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelRealization.CentralEmbedding
public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelRealization

/-!
# Application to the literal projection kernel

The certified central embedding discharges the three embedding premises of the
concrete kernel assembly. Only the independent order upper bound remains for
kernel exhaustion and the resulting perfect central covering.
Source: Aschbacher–Smith I.1.3(6), printed p.407; GLS3 §6.1.
-/

@[expose] public section
namespace Matrix.PSL3.ExceptionalFourCover.KernelModel

/-- The full multiplier embedded into the kernel of the actual projective map. -/
noncomputable def centralKernelEmbedding : Multiplier →* projection.ker :=
  kernelEmbedding centralEmbedding projection_comp_centralEmbedding

theorem centralKernelEmbedding_injective : Function.Injective centralKernelEmbedding :=
  kernelEmbedding_injective centralEmbedding projection_comp_centralEmbedding
    centralEmbedding_injective

/-- With the independent order certificate, the 48 central elements exhaust the kernel. -/
noncomputable def kernelEquivOfOrderBound (horder : Nat.card Group ≤ 967680) :
    projection.ker ≃* Multiplier :=
  kernelEquivOfEmbeddingAndOrder centralEmbedding projection_comp_centralEmbedding
    centralEmbedding_injective horder

/-- The explicit group becomes a perfect central cover once its order bound is certified. -/
noncomputable def perfectCoverOfOrderBound (horder : Nat.card Group ≤ 967680) :
    PerfectCentralCovering.Cover Group PSL3Four.PSL :=
  perfectCoverOfEmbeddingAndOrder centralEmbedding projection_comp_centralEmbedding
    centralEmbedding_injective centralEmbedding_central horder

end Matrix.PSL3.ExceptionalFourCover.KernelModel
