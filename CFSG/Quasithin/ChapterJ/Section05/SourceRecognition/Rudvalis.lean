module
public import CFSG.Quasithin.ChapterJ.Section05.SourceRecognition.Recognition
public import CFSG.Quasithin.ChapterJ.Section05.SourceModel

/-!
# The concrete Rudvalis conclusion of J.5.14

The independently checked concrete Rudvalis point-stabilizer action supplies
all comparison data, including the same native full-Ree local markings and
an actual element exchanging the first edge. Applying the original-action
uniqueness theorem therefore gives an isomorphism to the concrete carrier.
No recognition by group order or assumed graph isomorphism is used.

Source: Aschbacher–Smith J.5.14, printed p.449.
-/

@[expose] public section
noncomputable section
open MulAction
namespace CFSG.Quasithin.ChapterJ.Section05.RudvalisAction
variable {G:Type*} [Group G] [Finite G]
variable {F:Subgroup G} {q g:G} (hq:q∉F) (hs:q•(q•basePoint F)=basePoint F)
    (h:RudvalisAction F (q•basePoint F) (g•basePoint F))
include hq hs h

/-- J.5.14 with the actual concrete Rudvalis carrier: its independently checked
marked rank-three action discharges the comparison-group premise. -/
theorem nonempty_equiv_rudvalis : Nonempty (G≃*Rudvalis.Model) := by
  obtain ⟨r,k,hr,_,ht,⟨j⟩⟩:=SourceModel.exists_source_action
  exact h.source_group_equivalent hq hs hr ht j
end CFSG.Quasithin.ChapterJ.Section05.RudvalisAction
