module
public import CFSG.Quasithin.ChapterJ.Section05.SourceGeometry.Unique
public import CFSG.Quasithin.ChapterJ.Section05.SourceRecognition.NormalizedCoordinates

/-!
# Original adjacency from stabilizer orbit lengths

Native orbit cardinalities 780 and 975 characterize all cross-orbit adjacency.
The unique 975 orbit on the second suborbit is retained as an actual source
producer; no abstract rank-three graph is assumed.
-/

@[expose] public section
noncomputable section
open Subgroup MulAction
open ReeF4.Octagon.Binary
attribute [local instance] Automorphisms.FiniteBridge.pointAction
namespace CFSG.Quasithin.ChapterJ.Section05
attribute [local instance] canonicalSecondAction
variable {G:Type*} [Group G] [Finite G]
variable (F:Subgroup G) (q:G) (hq:q∉F) (hs:q•(q•basePoint F)=basePoint F) {g:G}
namespace RudvalisAction
variable (h:RudvalisAction F (q•basePoint F) (g•basePoint F))
include h

theorem base_second_first_adj_iff_card (x:orbit F (q•basePoint F)) :
    (sourceGraph F q hq hs).Adj (g•basePoint F) x.val ↔
      Nat.card (orbit (stabilizer F (g•basePoint F)) x.val)=780 := by
  have hx:(sourceGraph F q hq hs).Adj (basePoint F) x.val:=
    (sourceGraph_neighbor_base F q hq hs).ge x.property
  constructor
  · intro ha
    rw [h.common_neighbors_orbit F q hq hs ⟨x.val,hx,ha⟩]
    exact (h.parameters F q hq hs).2
  · intro hc
    rcases h.second_orbits_on_first F q hq hs hx with he|he
    · exact (he ▸ mem_orbit_self x.val).2
    · have h975:Nat.card (orbit (stabilizer F (g•basePoint F)) x.val)=975:=by
        rw [he]
        exact h.mixed_neighbors_card F q hq hs
      omega

theorem second_first_adj_iff_card (y:orbit F (g•basePoint F))
    (x:orbit F (q•basePoint F)) :
    (sourceGraph F q hq hs).Adj y.val x.val ↔
      Nat.card (orbit (stabilizer F y.val) x.val)=780 := by
  obtain ⟨k,hk⟩:=y.property
  change (k:G)•(g•basePoint F)=y.val at hk
  let x':orbit F (q•basePoint F):=k⁻¹•x
  have hkx:(k:G)•x'.val=x.val:=smul_inv_smul (k:G) x.val
  have he:=sourceGraph_adj_smul F q hq hs (k:G) (g•basePoint F) x'.val
  rw [hk,hkx] at he
  have hc:=suborbit_card_smul k (g•basePoint F) x'.val
  change Nat.card (orbit (stabilizer F ((k:G)•(g•basePoint F))) ((k:G)•x'.val))=_ at hc
  rw [hk,hkx] at hc
  rw [he,hc]
  exact h.base_second_first_adj_iff_card F q hq hs x'

theorem base_second_second_adj_iff_card (x:orbit F (g•basePoint F)) :
    (sourceGraph F q hq hs).Adj (g•basePoint F) x.val ↔
      Nat.card (orbit (stabilizer F (g•basePoint F)) x.val)=975 := by
  have hx:x.val∈sourceSigma F q hq hs (basePoint F):=
    (h.sigma_base F q hq hs).ge x.property
  constructor
  · intro ha
    rw [h.reverse_mixed_neighbors_orbit F q hq hs ⟨x.val,ha,hx⟩]
    exact h.reverse_mixed_neighbors_card F q hq hs
  · intro hc
    have he:=h.unique_reverse_mixed_orbit F q hq hs hx hc
    exact (he ▸ mem_orbit_self x.val).1

theorem second_second_adj_iff_card (y x:orbit F (g•basePoint F)) :
    (sourceGraph F q hq hs).Adj y.val x.val ↔
      Nat.card (orbit (stabilizer F y.val) x.val)=975 := by
  obtain ⟨k,hk⟩:=y.property
  change (k:G)•(g•basePoint F)=y.val at hk
  let x':orbit F (g•basePoint F):=k⁻¹•x
  have hkx:(k:G)•x'.val=x.val:=smul_inv_smul (k:G) x.val
  have he:=sourceGraph_adj_smul F q hq hs (k:G) (g•basePoint F) x'.val
  rw [hk,hkx] at he
  have hc:=suborbit_card_smul k (g•basePoint F) x'.val
  change Nat.card (orbit (stabilizer F ((k:G)•(g•basePoint F))) ((k:G)•x'.val))=_ at hc
  rw [hk,hkx] at hc
  rw [he,hc]
  exact h.base_second_second_adj_iff_card F q hq hs x'

end RudvalisAction

namespace NormalizedCoordinates
variable {F q} {h:RudvalisAction F (q•basePoint F) (g•basePoint F)} (c:NormalizedCoordinates h)

theorem first_adj_iff (x y:orbit F (q•basePoint F)) :
    (sourceGraph F q hq hs).Adj x.val y.val ↔
      c.point x≠c.point y ∧ pointDistance (c.point x) (c.point y)≠8 := by
  have ho:=h.local_opposition_iff F q hq hs x y
  rw [←c.point_distance x y] at ho
  rw [c.point.injective.ne_iff]
  constructor
  · intro ha
    refine ⟨fun he=>(sourceGraph F q hq hs).loopless.irrefl x.val (by simpa only [←he] using ha),?_⟩
    exact fun hh=>(ho.mp hh).2 ha
  · rintro ⟨hne,hn⟩
    by_contra ha
    exact hn (ho.mpr ⟨hne,ha⟩)

omit [Finite G] in
theorem second_first_orbit_card (y:orbit F (g•basePoint F))
    (x:orbit F (q•basePoint F)) :
    Nat.card (orbit (stabilizer F y.val) x.val)=
      Nat.card (orbit (stabilizer (ReeF4.Model 0) (c.second y)) (c.point x)) := by
  have he:(stabilizer F y.val).map c.actor.toMonoidHom=
      stabilizer (ReeF4.Model 0) (c.second y):=by
    rw [←stabilizer_orbitSubtype y]
    exact stabilizer_map_of_equivariant c.actor c.second c.second_smul y
  rw [←orbitSubtype_card (stabilizer F y.val) x]
  have hc:=orbit_card_of_equivariant c.actor c.point c.point_smul (stabilizer F y.val) x
  rwa [he] at hc

omit [Finite G] in
theorem second_second_orbit_card (y x:orbit F (g•basePoint F)) :
    Nat.card (orbit (stabilizer F y.val) x.val)=
      Nat.card (orbit (stabilizer (ReeF4.Model 0) (c.second y)) (c.second x)) := by
  have he:(stabilizer F y.val).map c.actor.toMonoidHom=
      stabilizer (ReeF4.Model 0) (c.second y):=by
    rw [←stabilizer_orbitSubtype y]
    exact stabilizer_map_of_equivariant c.actor c.second c.second_smul y
  rw [←orbitSubtype_card (stabilizer F y.val) x]
  have hc:=orbit_card_of_equivariant c.actor c.second c.second_smul (stabilizer F y.val) x
  rwa [he] at hc
end NormalizedCoordinates
end CFSG.Quasithin.ChapterJ.Section05
