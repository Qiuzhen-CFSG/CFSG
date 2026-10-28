module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.Transfer.SpanBound.Cocycle
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.Transfer.SpanBound.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.Transfer.SpanBound.Extension
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.Transfer.SpanBound.Sharpening

/-!
# The marked-module span bound in MS93 (4.2)(i)

In the distance-four case, the neighboring B_alpha containments put the
whole neighboring displacement span in [Z_alpha,Q_beta] D_alpha. Equal
kernels identify the Z-layers. For unequal kernels, the actual marked
quotient and the binary nonsplit-extension calculation first place the
neighboring displacement in U_alpha D_alpha. The edge action then sharpens
this bound, using the order-four displacement proved from the initial facts.

This is the first, marked-module part of (4.2)(i). The characteristic
centralizer argument in `Transfer.edge_transfer_of_span` consumes exactly
this bound to obtain the source's final fixed-subgroup conclusion.

Source: Meierfrankenfeld--Stellmacher (1993), (1.5)(i) and (4.2)(i),
printed pp.843 and 882.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.Transfer
variable {M : Type*} [Group M] [Finite M] (R : Subgroup M)
  {L : Subgroup M} {source : LocalSource L R} {geometry : Geometry R}
  (common : CommonFacts R source geometry)

include common in
/-- The marked-module containment in MS93 (4.2)(i), specialized to critical
distance four. The extension realization and edge-action sharpening are
discharged from the source data and the initial distance-four facts. -/
theorem edgeSpan_le_displacement_sup_fixedCore
    (hb : geometry.b R = 4) (initial : InitialFacts R geometry)
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b)
    (hB : ∀ d, Adjacent R d b → ⁅Z R d, Q R b⁆ ≤ B R a (geometry.Z_normal a)) :
    edgeSpan R b ≤ ⁅Z R a, Q R b⁆ ⊔ fixedCore R a := by
  apply SpanBound.edgeSpan_le_of_neighbor_steps common a b ha hab hB
  · intro d hdb hne hBd
    exact SpanBound.Extension.neighbor_le_natural_sup_fixedCore common
      a b d ha hab hdb hne hBd
  · intro d hdb hne hnatural
    exact SpanBound.neighbor_displacement_le_edge_sup_fixedCore common hb initial
      a b d ha hab hdb hne hB hnatural

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.Transfer
