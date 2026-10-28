module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.EdgeTransfer.Assembly
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.EdgeTransfer.Extension
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.EdgeTransfer.Sharpening
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.EdgeTransfer.Sharpening.Source

/-!
# The general binary edge transfer

The actual marked neighboring extension supplies the natural-module bound.
An edge displacement of order two is central in the edge kernel. In the
order-four case, the natural bound sharpens to containment in the edge
displacement times the fixed core; equal local kernels identify their
omega-centers directly. The resulting characteristic span and its intrinsic
centralizer let source minimality force centralization by the whole edge
kernel, giving the required containment in its omega-center.

`edgeTransfer` discharges every extra premise of the general binary (4.2)(i)
argument from LocalSource, Geometry, b > 2, and ModuleFacts. The earlier
conditional assembly remains available as a separate interface.

Source: Meierfrankenfeld--Stellmacher (1993), (4.2)(i), printed p.882.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.EdgeTransfer
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Conditional assembly using both neighboring bounds. The source theorem
`edgeTransfer` below also handles order-two displacement directly. -/
theorem edgeTransfer_of_neighbor_steps (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (hext : NeighborNaturalBound geometry) (hsharp : NeighborSharpening geometry) :
    Escape.EdgeTransfer geometry := by
  intro a b ha hab hB
  apply edge_transfer_of_span R hb modules a b ha hab
  apply edgeSpan_le_of_neighbor_steps modules a b ha hab hB
  · exact fun d hdb hne hBd => hext a b d ha hab hdb hne hBd
  · exact fun d hdb hne hnatural => hsharp a b d ha hab hdb hne hB hnatural

/-- MS93 (4.2)(i), printed p.882, in the binary case: if every neighboring
edge displacement lies in B_alpha, then the alpha displacement lies in Z_beta.
The marked-extension bound and both edge-action cases are proved from the
source module data, with no escape or critical-distance-four premise. -/
theorem edgeTransfer (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) : Escape.EdgeTransfer geometry := by
  exact Sharpening.edgeTransfer_of_neighbor_naturalBound hb modules
    (neighborNaturalBound hb modules)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.EdgeTransfer
