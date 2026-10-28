module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.RadiusChiefControl
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.CriticalImage
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.CriticalEvenActor

/-!
# Centrality and radius bounds in the actual binary symplectic source

If the radius commutator is not central, a pair of its generators selects a
critical path with forward image of order at least four. The actual natural
module forces a reverse even involution. The marked point-core calculation
and the radius image bound give fixed index at most eight on V/Z; the
nonabelian chief-factor budget and abelian edge argument then force centrality.

This closes the distance-four case. Greater distances use the earlier
radius-abelianity argument, and conjugation gives every original-group vertex.
The derived-radius and critical triple-commutator bounds follow. The final
applications use the literal original characteristic replacement and discharge
all marked, actor, index, chief-count and edge-generation inputs internally.

Source: Meierfrankenfeld--Stellmacher (1993), (5.2), printed pp.914--915.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
namespace Source
variable {M : Type*} [Group M] [Finite M]
  {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)

/-- The genuine source (5.2)(ii) centrality assertion at critical distance four. -/
theorem radius_commutator_central_of_b_eq_four (h : NativeCentralLayer s)
    (u : S) (hR : R.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (hb : s.geometry.b R = 4) :
    ⁅V R (alpha R),Q R (alpha R)⁆ ≤ centralizer (V R (alpha R) : Set (FreeAmalgam R)) := by
  by_contra hn
  obtain ⟨e,p,hforward⟩ := s.exists_base_large_critical_path hb hn
  obtain ⟨a,haA,ha,heven⟩ :=
    s.exists_even_involution_reverse_critical_image h (by omega) p hforward
  exact hn (s.critical_radius_central_of_marked_actor u hR hb p a ha heven haA
    (s.critical_radius_commutator_le_Z h u hR hb p hforward))

/-- Both the distance-four and greater-distance branches of source (5.2)(ii). -/
theorem radius_commutator_central_of_two_lt (h : NativeCentralLayer s)
    (u : S) (hR : R.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < s.geometry.b R) :
    ⁅V R (alpha R),Q R (alpha R)⁆ ≤ centralizer (V R (alpha R) : Set (FreeAmalgam R)) := by
  by_cases hlarge : 4 < s.geometry.b R
  · exact SectionFive.radius_commutator_central_of_four_lt R s.geometry hlarge rfl
  · have heven : Even (s.geometry.b R) := s.geometry.even (alpha R) rfl
    rw [Nat.even_iff] at heven
    exact s.radius_commutator_central_of_b_eq_four h u hR (by omega)

/-- The same centrality at every original-group vertex, through literal graph conjugation. -/
theorem radius_commutator_central_at (h : NativeCentralLayer s)
    (u : S) (hR : R.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < s.geometry.b R) (a : Vertex R) (ha : color R a = false) :
    ⁅V R a,Q R a⁆ ≤ centralizer (V R a : Set (FreeAmalgam R)) := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color R ha
  have hV : V R (mVertex R g) = (V R (alpha R)).map (MulAut.conj g⁻¹).toMonoidHom := by
    simpa only [alpha,act_mVertex,one_mul] using V_act R g (alpha R)
  have hQ : Q R (mVertex R g) = (Q R (alpha R)).map (MulAut.conj g⁻¹).toMonoidHom := by
    simpa only [alpha,act_mVertex,one_mul] using Q_act R g (alpha R)
  rw [hV,hQ,←map_commutator]
  exact (map_mono (s.radius_commutator_central_of_two_lt h u hR hb)).trans
    (map_centralizer_le_centralizer_image (V R (alpha R) : Set (FreeAmalgam R))
      (MulAut.conj g⁻¹).toMonoidHom)

/-- All three source (5.2)(ii)--(iii) radius conclusions, with no additional
centrality, quotient, actor or chief-factor premise. -/
theorem radius_bounds_of_two_lt (h : NativeCentralLayer s)
    (u : S) (hR : R.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < s.geometry.b R) {a : Vertex R} (ha : color R a = false)
    (a' c : Vertex R) :
    ⁅V R a,Q R a⁆ ≤ centralizer (V R a : Set (FreeAmalgam R)) ∧
    ⁅V R a,V R a⁆ ≤ X R a ∧
    ⁅⁅X R a' ⊓ Q R a,V R a ⊓ Q R c⁆,V R a ⊓ Q R c⁆ = ⊥ := by
  have hc := s.radius_commutator_central_at h u hR hb a ha
  exact ⟨hc,s.radius_bounds_of_central hb ha hc a' c⟩
end Source

namespace SourceData
variable {K : Type*} [Group K] [Finite K]
  {L W : Subgroup K} [L.Normal] [W.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L W T)

/-- The original characteristic replacement supplies every premise of radius
commutator centrality in the source branch b > 2. -/
theorem reducedSource_radius_commutator_central (h : IntrinsicMSPair d)
    (c : CharacteristicReduction (L.subgroupOf (L ⊔ d.B))
      (d.B.subgroupOf (L ⊔ d.B)))
    (hb : 2 < ((originalSource d h).reduce c).geometry.b c.radical) :
    ⁅V c.radical (alpha c.radical),Q c.radical (alpha c.radical)⁆ ≤
      centralizer (V c.radical (alpha c.radical) : Set (FreeAmalgam c.radical)) :=
  Source.radius_commutator_central_of_two_lt ((originalSource d h).reduce c)
    (reduced_nativeCentralLayer d h c) d.relabeler.val⁻¹
    (reducedSource_radical_image_le d h c) hb

/-- Literal original-source application of the complete radius conclusions. -/
theorem reducedSource_radius_bounds_of_two_lt (h : IntrinsicMSPair d)
    (c : CharacteristicReduction (L.subgroupOf (L ⊔ d.B))
      (d.B.subgroupOf (L ⊔ d.B)))
    (hb : 2 < ((originalSource d h).reduce c).geometry.b c.radical)
    (a' e : Vertex c.radical) :
    ⁅V c.radical (alpha c.radical),Q c.radical (alpha c.radical)⁆ ≤
      centralizer (V c.radical (alpha c.radical) : Set (FreeAmalgam c.radical)) ∧
    ⁅V c.radical (alpha c.radical),V c.radical (alpha c.radical)⁆ ≤
      X c.radical (alpha c.radical) ∧
    ⁅⁅X c.radical a' ⊓ Q c.radical (alpha c.radical),
        V c.radical (alpha c.radical) ⊓ Q c.radical e⁆,
      V c.radical (alpha c.radical) ⊓ Q c.radical e⁆ = ⊥ := by
  have hc := reducedSource_radius_commutator_central d h c hb
  exact ⟨hc,reducedSource_radius_bounds d h c hb hc a' e⟩
end SourceData
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
