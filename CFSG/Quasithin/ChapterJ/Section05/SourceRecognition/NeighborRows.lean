module
public import CFSG.Quasithin.ChapterJ.Section05.SourceRecognition.SecondStabilizer
public import CFSG.Quasithin.ChapterJ.Section05.SourceGeometry.Sigma
public import Theory.GroupAction.PrimitiveIncidence

/-!
# Faithfulness on the original neighbor set

The second point stabilizer is maximal. Its nonempty proper common-neighbor
row therefore has precisely that stabilizer, so different second-orbit points
have different rows. This proves that an original graph automorphism fixing the
base and all its neighbors is trivial.
Source: Aschbacher–Smith J.5.6, printed p.447.
-/

@[expose] public section
noncomputable section
open Subgroup MulAction
open scoped Pointwise
namespace CFSG.Quasithin.ChapterJ.Section05
variable {G:Type*} [Group G] [Finite G]
variable (F:Subgroup G) (q:G) (hq:q∉F) (hs:q•(q•basePoint F)=basePoint F) {g:G}

def secondNeighborRow (y:orbit F (g•basePoint F)) : Set (orbit F (q•basePoint F)) :=
  {x | (sourceGraph F q hq hs).Adj y.val x.val}

omit [Finite G] in
theorem secondNeighborRow_smul (f:F) (y:orbit F (g•basePoint F)) :
    secondNeighborRow F q hq hs (f•y)=f•secondNeighborRow F q hq hs y := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  change (sourceGraph F q hq hs).Adj ((f:G)•y.val) x.val ↔
    (sourceGraph F q hq hs).Adj y.val ((f:G)⁻¹•x.val)
  have hh:=sourceGraph_adj_smul F q hq hs (f:G) y.val ((f:G)⁻¹•x.val)
  simpa only [smul_inv_smul] using hh

namespace RudvalisAction
variable (h:RudvalisAction F (q•basePoint F) (g•basePoint F))
include h

private theorem row_card :
    Nat.card (secondNeighborRow F q hq hs ⟨g•basePoint F,mem_orbit_self _⟩)=780 := by
  let e : secondNeighborRow F q hq hs ⟨g•basePoint F,mem_orbit_self _⟩ ≃
      (sourceGraph F q hq hs).commonNeighbors (basePoint F) (g•basePoint F) :=
    { toFun := fun x=>⟨x.val.val,⟨(sourceGraph_neighbor_base F q hq hs).ge x.val.property,x.property⟩⟩
      invFun := fun x=>⟨⟨x.val,(sourceGraph_neighbor_base F q hq hs).le x.property.1⟩,x.property.2⟩
      left_inv := fun _=>rfl
      right_inv := fun _=>rfl }
  exact (Nat.card_congr e).trans (h.parameters F q hq hs).2

/-- Common-neighbor rows in the first orbit distinguish every second-orbit point. -/
theorem secondNeighborRows_injective : Function.Injective (secondNeighborRow F q hq hs (g:=g)) := by
  let y0:orbit F (g•basePoint F):=⟨g•basePoint F,mem_orbit_self _⟩
  apply incidence_rows_injective _ (secondNeighborRow_smul F q hq hs) y0
  · have he : stabilizer F y0=stabilizer F (g•basePoint F) := by
      ext f
      change f•y0=y0 ↔ f•(g•basePoint F)=g•basePoint F
      exact Subtype.ext_iff
    rw [he]
    exact h.second_stabilizer_isCoatom
  · have hc:=h.row_card F q hq hs
    change Nat.card (secondNeighborRow F q hq hs y0)=780 at hc
    have hn:Nonempty (secondNeighborRow F q hq hs y0) :=
      (Nat.card_pos_iff.mp (by omega)).1
    obtain ⟨x⟩:=hn
    exact ⟨x.val,x.property⟩
  · intro he
    have hc:=h.row_card F q hq hs
    change Nat.card (secondNeighborRow F q hq hs y0)=780 at hc
    rw [he,Nat.card_congr (Equiv.Set.univ _),h.first_length] at hc
    contradiction

/-- Literal source form of the uniqueness assertion in the first paragraph of J.5.6. -/
theorem second_points_eq_of_common_neighbors {x y:Cosets F}
    (hx:x∈sourceSigma F q hq hs (basePoint F))
    (hy:y∈sourceSigma F q hq hs (basePoint F))
    (he:∀z∈orbit F (q•basePoint F),
      (sourceGraph F q hq hs).Adj x z ↔ (sourceGraph F q hq hs).Adj y z) : x=y := by
  let x':orbit F (g•basePoint F):=⟨x,(h.sigma_base F q hq hs).le hx⟩
  let y':orbit F (g•basePoint F):=⟨y,(h.sigma_base F q hq hs).le hy⟩
  have hh : secondNeighborRow F q hq hs x'=secondNeighborRow F q hq hs y' := by
    ext z
    exact he z.val z.property
  exact congrArg Subtype.val (h.secondNeighborRows_injective F q hq hs hh)

/-- A graph automorphism fixing the base and its entire neighbor set is trivial. -/
theorem fix_base_neighbors_eq_refl
    (a:sourceGraph F q hq hs ≃g sourceGraph F q hq hs)
    (ha:a (basePoint F)=basePoint F)
    (hf:∀x∈orbit F (q•basePoint F),a x=x) : a=SimpleGraph.Iso.refl := by
  ext x : 1
  change a x=x
  by_cases hx:x=basePoint F
  · simpa only [hx] using ha
  by_cases hd:x∈orbit F (q•basePoint F)
  · exact hf x hd
  have hxS:x∈sourceSigma F q hq hs (basePoint F) :=
    ⟨hx,fun hh=>hd ((sourceGraph_neighbor_base F q hq hs).le hh)⟩
  have haS:a x∈sourceSigma F q hq hs (basePoint F) := by
    refine ⟨fun he=>hx (a.injective (he.trans ha.symm)),?_⟩
    intro he
    apply hxS.2
    apply a.map_adj_iff.mp
    rwa [ha]
  apply h.second_points_eq_of_common_neighbors F q hq hs haS hxS
  intro z hz
  have hh:=a.map_adj_iff (v:=x) (w:=z)
  rwa [hf z hz] at hh
end RudvalisAction
end CFSG.Quasithin.ChapterJ.Section05
