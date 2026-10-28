module
public import CFSG.Quasithin.ChapterJ.Section05.SourceRecognition.Automorphisms
public import Theory.GroupAction.MarkedOrbit

/-!
# Simultaneous native coordinates for both source suborbits

The native conjugacy theorem normalizes the actual second stabilizer. Shifting
the first coordinates by the same conjugation preserves their group action
and building distances. The original three-orbit partition then gives the
common vertex set used in J.5.13.
-/

@[expose] public section
noncomputable section
open Subgroup MulAction
open ReeF4.Octagon.Binary
attribute [local instance] Automorphisms.FiniteBridge.pointAction
namespace CFSG.Quasithin.ChapterJ.Section05
open Tits.ExceptionalParabolics.FullRee

abbrev CanonicalSecond := (ReeF4.Model 0)⧸FiveOvergroups.candidateNormalizer

local instance canonicalSecondAction : MulAction (ReeF4.Model 0) CanonicalSecond :=
  @MulAction.quotient (ReeF4.Model 0) (ReeF4.Model 0) (ReeF4.modelGroup 0) inferInstance
    (Monoid.toMulAction _) FiveOvergroups.candidateNormalizer (MulAction.left_quotientAction _)

variable {G:Type*} [Group G]
variable {F:Subgroup G} {q g:G}

/-- Coordinates for both unchanged suborbits, with the second stabilizer
normalized to the fixed native normalizer and the first coordinates shifted
by the same group conjugation. -/
structure NormalizedCoordinates
    (h:RudvalisAction F (q•basePoint F) (g•basePoint F)) where
  actor : F≃*ReeF4.Model 0
  point : orbit F (q•basePoint F)≃PointCoset
  second : orbit F (g•basePoint F)≃CanonicalSecond
  point_smul : ∀f v,point (f•v)=actor f•point v
  second_smul : ∀f v,second (f•v)=actor f•second v
  second_base : second ⟨g•basePoint F,mem_orbit_self _⟩=(1:ReeF4.Model 0)
  point_distance : ∀u v,pointDistance (point u) (point v)=
    pointDistance (h.pointEquiv u) (h.pointEquiv v)

namespace RudvalisAction
variable (h:RudvalisAction F (q•basePoint F) (g•basePoint F))

theorem exists_normalizedCoordinates : Nonempty (NormalizedCoordinates h) := by
  let J:Subgroup (ReeF4.Model 0):=(stabilizer F (g•basePoint F)).map h.marking.toMonoidHom
  have hc:Nat.card J=15600:=by
    rw [card_map_of_injective h.marking.injective]
    exact h.second_stabilizer_card F q
  have hD:¬commutator (ReeF4.Model 0)≤J:=by
    intro he
    have hd:Nat.card (commutator (ReeF4.Model 0))=17971200:=
      (Nat.card_congr atlasDerivedEquiv.toEquiv).symm.trans Tits.atlas1600Group_card
    have hh:=card_le_of_le he
    rw [hd,hc] at hh
    omega
  obtain ⟨_,a,ha⟩:=FiveOvergroups.large_conjugate_normalizer J hD (by rw [hc]; decide) hc.ge
  let t:=atlasEmbedding a
  let e:=h.marking.trans (MulAut.conj t)
  have hE:(stabilizer F (g•basePoint F)).map e.toMonoidHom=
      FiveOvergroups.candidateNormalizer:=by
    change (stabilizer F (g•basePoint F)).map
      ((MulAut.conj t).toMonoidHom.comp h.marking.toMonoidHom)=_
    rw [←map_map]
    exact ha
  let f:=h.pointEquiv.trans (MulAction.toPerm t)
  refine ⟨{
    actor := e
    point := f
    second :=markedOrbitEquiv e (g•basePoint F) FiveOvergroups.candidateNormalizer hE
    point_smul := ?_
    second_smul := markedOrbitEquiv_smul _ _ _ _
    second_base := markedOrbitEquiv_base _ _ _ _
    point_distance := ?_ }⟩
  · intro k v
    change t•h.pointEquiv (k•v)=(t*h.marking k*t⁻¹)•(t•h.pointEquiv v)
    rw [h.pointEquiv_smul]
    simp only [mul_smul,inv_smul_smul]
  · intro u v
    exact pointDistance_smul t _ _
end RudvalisAction

abbrev CanonicalVertex : Type := PUnit ⊕ (PointCoset ⊕ CanonicalSecond)

namespace NormalizedCoordinates
variable {h:RudvalisAction F (q•basePoint F) (g•basePoint F)} (c:NormalizedCoordinates h)
variable (hq:q∉F)

def vertex : CanonicalVertex→Cosets F
  | .inl _=>basePoint F
  | .inr (.inl p)=>(c.point.symm p).val
  | .inr (.inr s)=>(c.second.symm s).val

include hq in
private theorem point_ne_base (p:PointCoset) :
    (c.point.symm p).val≠basePoint F := by
  intro he
  apply basePoint_not_mem_orbit hq
  have hp:=(c.point.symm p).property
  rwa [he] at hp

private theorem second_ne_base (s:CanonicalSecond) :
    (c.second.symm s).val≠basePoint F := by
  have hx:=h.partition.le (c.second.symm s).property
  intro he
  exact hx (Or.inl he)

private theorem second_ne_point (s:CanonicalSecond) (p:PointCoset) :
    (c.second.symm s).val≠(c.point.symm p).val := by
  have hx:=h.partition.le (c.second.symm s).property
  intro he
  exact hx (Or.inr (he.symm ▸ (c.point.symm p).property))

include hq in
theorem vertex_injective : Function.Injective c.vertex := by
  intro u v he
  rcases u with u | (u|u) <;> rcases v with v | (v|v)
  · rfl
  · exact False.elim (c.point_ne_base hq v he.symm)
  · exact False.elim (c.second_ne_base v he.symm)
  · exact False.elim (c.point_ne_base hq u he)
  · exact congrArg (fun p:PointCoset=>Sum.inr (Sum.inl p))
      (c.point.symm.injective (Subtype.ext he))
  · exact False.elim (c.second_ne_point v u he.symm)
  · exact False.elim (c.second_ne_base u he)
  · exact False.elim (c.second_ne_point u v he)
  · exact congrArg (fun s:CanonicalSecond=>Sum.inr (Sum.inr s))
      (c.second.symm.injective (Subtype.ext he))

theorem vertex_surjective : Function.Surjective c.vertex := by
  intro x
  by_cases hb:x=basePoint F
  · exact ⟨.inl PUnit.unit,hb.symm⟩
  by_cases hp:x∈orbit F (q•basePoint F)
  · refine ⟨.inr (.inl (c.point ⟨x,hp⟩)),?_⟩
    change (c.point.symm (c.point ⟨x,hp⟩)).val=x
    rw [c.point.symm_apply_apply]
  · have hs:x∈orbit F (g•basePoint F):=by
      rw [h.partition]
      exact fun hx=>hx.elim hb hp
    refine ⟨.inr (.inr (c.second ⟨x,hs⟩)),?_⟩
    change (c.second.symm (c.second ⟨x,hs⟩)).val=x
    rw [c.second.symm_apply_apply]

def vertexEquiv : CanonicalVertex≃Cosets F :=
  Equiv.ofBijective c.vertex ⟨c.vertex_injective hq,c.vertex_surjective⟩

theorem vertexEquiv_base : c.vertexEquiv hq (.inl PUnit.unit)=basePoint F:=rfl
theorem vertexEquiv_point (p:PointCoset) :
    c.vertexEquiv hq (.inr (.inl p))=(c.point.symm p).val:=rfl
theorem vertexEquiv_second (s:CanonicalSecond) :
    c.vertexEquiv hq (.inr (.inr s))=(c.second.symm s).val:=rfl
end NormalizedCoordinates

end CFSG.Quasithin.ChapterJ.Section05
