module
public import CFSG.Quasithin.ChapterJ.Section05.SourceGeometry.Mixed
public import CFSG.Quasithin.ChapterJ.Section05.SourceGeometry.Socle
public import Theory.GroupAction.ThirteenOrbitArithmetic.Unique

/-!
# The unique975-point second-stabilizer orbit on Sigma

The preceding native subgroup calculation is applied only after the actual
socle exception has been excluded. Two hypothetical975-point orbits, together
with the fixed point, would leave an invariant set of353 points. The corrected
thirteen-overgroup arithmetic rules this out. All sets and actions are the
original coset objects, and the reversed mixed set is identified literally.

Source: Aschbacher–Smith J.5.5(5), printed p.447.
-/

public noncomputable section
open Subgroup MulAction
namespace CFSG.Quasithin.ChapterJ.Section05.RudvalisAction
variable {G:Type*} [Group G] [Finite G] (F:Subgroup G) (q:G) (hq:q∉F)
    (hs:q•(q•basePoint F)=basePoint F) {g:G}
    (h:RudvalisAction F (q•basePoint F) (g•basePoint F))

include h

/-- J.5.5(5): the literal reversed mixed set is the unique975-point orbit on Sigma. -/
theorem unique_reverse_mixed_orbit {x:Cosets F}
    (hx:x∈sourceSigma F q hq hs (basePoint F))
    (hcard:Nat.card (orbit (stabilizer F (g•basePoint F)) x)=975) :
    orbit (stabilizer F (g•basePoint F)) x=
      (sourceGraph F q hq hs).neighborSet (g•basePoint F)∩sourceSigma F q hq hs (basePoint F) := by
  let E:=stabilizer F (g•basePoint F)
  let S:=sourceSigma F q hq hs (basePoint F)
  let B:Set (Cosets F):=(sourceGraph F q hq hs).neighborSet (g•basePoint F)∩S
  have hb:B.ncard=975:=h.reverse_mixed_neighbors_card F q hq hs
  have hbn:B.Nonempty:=by
    by_contra hn
    have he:B=∅:=Set.not_nonempty_iff_eq_empty.mp hn
    simp [he] at hb
  obtain ⟨y,hy⟩:=hbn
  have hycard:Nat.card (orbit E y)=975:=by
    rw [h.reverse_mixed_neighbors_orbit F q hq hs ⟨y,hy⟩]
    exact hb
  have hS:∀k:E,∀z∈S,k•z∈S:=by
    intro k z hz
    have hh:=(sourceSigma_smul F q hq hs (k.val:G) (basePoint F) z).mpr hz
    have hk0:(k.val:G)•basePoint F=basePoint F:=basePoint_fixed F k.val
    rwa [hk0] at hh
  have hsize:Nat.card S=2304:=by
    change Nat.card (sourceSigma F q hq hs (basePoint F))=2304
    rw [h.sigma_base F q hq hs];exact h.second_length
  have he:=unique_orbit_975_of_thirteen_alternatives S (g•basePoint F) hS hsize
    (h.second_mem_sigma F q hq hs) (fun k:E=>k.property)
    (fun z hz hne=>h.sigma_orbit_card_alternatives F q hq hs hz hne) x y hx hy.2 hcard hycard
  exact he.trans (h.reverse_mixed_neighbors_orbit F q hq hs ⟨y,hy⟩)

end CFSG.Quasithin.ChapterJ.Section05.RudvalisAction
