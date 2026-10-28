module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.PointCovers
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.PointEvenRankTwo
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.PointSporadicComplete
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.ThreeExclusion

/-!
# The remaining point-component models in the exterior source argument

Apply the full known-simple A.3.6 catalogue to the actual normal component
image in G₁/O₂(G₁), preserving its quotient equivalence and the original
Sylow restriction. The proved simple-model sieve and the central A₆ and
M₂₂-cover exclusions leave only the signed odd ternary models and 3.A₇.
Every other row supplies the original point alternative, including Y ≤ K₁
in the large rows and the literal Ξ₇ product in the radical row.

The final consumer constructs LocalComponents from that alternative.
Thus the original hypotheses either construct all four local components,
with their relative normality, or give an actual normal point component
in one of the two remaining families. This is a reduction, not an
unconditional proof of 12.5.3. Their exclusion, the general normalizer
containments and quasisimple strict enlargement remain with qt-d-1251-local;
qt-d-1251-source retains final exterior assembly.
Source: Aschbacher--Smith 12.5.3, printed pp.817--819, and A.3.6, pp.43--45.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

private theorem rankTwoModel_transport {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (hm : RankTwoTheoremC Y) : RankTwoTheoremC X := by
  cases hm with
  | linear n hn hm => exact .linear n hn (hm.of_mulEquiv e)
  | symplectic n hn hm => exact .symplectic n hn (hm.of_mulEquiv e)
  | g2 n hn hm => exact .g2 n hn (hm.of_mulEquiv e)
  | triality n hn hm => exact .triality n hn (hm.of_mulEquiv e)
  | ree n hn hm =>
    obtain ⟨d,⟨a⟩⟩ := hm
    exact .ree n hn ⟨d,⟨e.trans a⟩⟩
  | symplectic_derived hm => exact .symplectic_derived (hm.map fun a => e.trans a)
  | g2_derived hm => exact .g2_derived (hm.map fun a => e.trans a)
  | tits hm => exact .tits (hm.map fun a => e.trans a)

private theorem threeCover_transport {X Y : Type*} [Group X] [Group Y]
    {Z : Type} [Group Z] (e : X ≃* Y) (hm : IsThreeCover Y Z) : IsThreeCover X Z := by
  let := hm.1
  have hz : (center X).map e.toMonoidHom = center Y := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩
  exact ⟨IsQuasisimple.of_mulEquiv e.symm,
    hm.2.1.map (fun a => (centerCongr e).trans a),
    hm.2.2.map (fun a => (QuotientGroup.congr _ _ e hz).trans a)⟩

private theorem slSign_transport {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) {unitary : Bool} {n q : ℕ}
    (hm : IsSLSign Y unitary n q) : IsSLSign X unitary n q := by
  cases unitary
  · obtain ⟨F,hF,hfin,hcard,⟨a⟩⟩ := hm
    exact ⟨F,hF,hfin,hcard,⟨e.trans a⟩⟩
  · obtain ⟨F,hF,hfin,J,hcard,hconj,⟨a⟩⟩ := hm
    exact ⟨F,hF,hfin,J,hcard,hconj,⟨e.trans a⟩⟩

private theorem pslSign_transport {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) {unitary : Bool} {n q : ℕ}
    (hm : IsPSLSign Y unitary n q) : IsPSLSign X unitary n q := by
  cases unitary
  · exact ClassicalGroup.IsPSL.of_mulEquiv hm e
  · exact ClassicalGroup.IsPSU.of_mulEquiv hm e


/-- The two unresolved families in the point-component sieve, on its actual quotient. -/
@[expose] def RemainingPointModel (Q : Type*) [Group Q] : Prop :=
  (∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ unitary : Bool,
    IsPSLSign Q unitary 3 p ∨ IsSLSign Q unitary 3 p) ∨ IsAlternatingCover Q 7

private theorem point_alternative_or_remaining_of_simple_catalogue
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    {X : Type*} [Group X] (e : (K ⧸ pCore 2 K) ≃* X)
    (hm : TheoremCModel X) :
    LocalComponentAlternative s 1 K ∨ RemainingPointModel (K ⧸ pCore 2 K) := by
  cases hm with
  | alternating n hn hm =>
    exact (s.point_component_not_alternating h hK hLK hN hn
      (hm.map fun a => e.trans a)).elim
  | linear_odd p d hp ho hd _ hm =>
    exact .inl (.equal (s.point_component_eq_of_odd_linear hK hLK hp ho hd (hm.of_mulEquiv e)))
  | three_odd p hp ho unitary hm =>
    exact .inr (.inl ⟨p,hp,ho,unitary,.inl (pslSign_transport e hm)⟩)
  | rank_one hm =>
    exact .inl (.equal (s.point_component_eq_of_bender hK hLK (hm.of_mulEquiv e)))
  | rank_two hm =>
    exact .inl (.equal (s.point_component_eq_of_even_rank_two h hK hLK hN
      (rankTwoModel_transport e hm)))
  | binary_linear n hn hm =>
    exact .inl (s.local_point_component_alternative_of_binary_linear h hK hLK hN hn
      (hm.of_mulEquiv e))
  | sporadic name hj hm =>
    exact .inl (s.local_point_component_alternative_of_sporadic h hK hLK hN
      name hj (hm.map fun a => e.trans a))
  | janko_one hm =>
    exact (s.point_component_not_jankoOne hLK (hm.map fun a => e.trans a)).elim

private theorem point_alternative_or_remaining_of_cover_catalogue
    {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K)
    {X : Type*} [Group X] (e : (K ⧸ pCore 2 K) ≃* X)
    (hm : ThreeCoverModel X) :
    LocalComponentAlternative s 1 K ∨ RemainingPointModel (K ⧸ pCore 2 K) := by
  cases hm with
  | classical unitary q hq hm =>
    have hm' := slSign_transport e hm
    rcases hq with ⟨n,hn,rfl,_⟩ | ⟨hp,ho⟩
    · exact .inl (.equal (s.point_component_eq_of_even_classical_cover hK hLK hn unitary hm'))
    · exact .inr (.inl ⟨q,hp,ho,unitary,.inr hm'⟩)
  | alternating_six hm =>
    exact (s.point_component_not_alternating_six_cover hLK (threeCover_transport e hm)).elim
  | alternating_seven hm =>
    exact .inr (.inr (threeCover_transport e hm))
  | mathieu hm =>
    exact (s.point_component_not_mathieu_cover hK hLK (threeCover_transport e hm)).elim

/-- The complete source catalogue leaves only odd ternary and triple-A₇ point quotients. -/
theorem point_component_alternative_or_remaining
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal) :
    LocalComponentAlternative s 1 K ∨ RemainingPointModel (K ⧸ pCore 2 K) := by
  by_cases hq : IsQuasisimple (K ⧸ pCore 2 K)
  · let Q := s.marking.Gi 1 ⧸ pCore 2 (s.marking.Gi 1)
    let C := s.pointCoreImage K
    let e := s.pointComponentCoreEquivImage hK.1 hN
    let := hq
    let : IsQuasisimple C := IsQuasisimple.of_mulEquiv e
    let : Group.IsNilpotent (pCore 2 (s.marking.Gi 1)) := pCore_isNilpotent
    have hC : C.IsCComponent := hK.2.map_quotient (pCore 2 (s.marking.Gi 1))
    have hQ : IsSQTK KnownSimple.IsKnownSimple Q := ChapterE.Structure.sqtk_two_quotient
      (h.simpleQTKE.twoLocal_sqtk (s.marking.Gi_twoLocal 1 (.inl rfl)))
      (pCore 2 (s.marking.Gi 1)) pCore_isPGroup
    rcases ChapterA.Section03.SourceEmbeddings.quasisimple_containing_component_models_knownSimple
      hQ (pCore_quotient_pCore_eq_bot 2) hC with ⟨_,hm⟩ | ⟨_,hm⟩
    · exact s.point_alternative_or_remaining_of_simple_catalogue h hK hLK hN e hm
    · exact s.point_alternative_or_remaining_of_cover_catalogue hK hLK e hm
  · exact .inl (s.local_point_component_radical_alternative h hK hLK hq)

/-- Original hypotheses construct all local components or an actual normal point
component in one of the two remaining model families. -/
theorem local_components_or_remaining_point_model
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    Nonempty (LocalComponents s) ∨ ∃ K : Subgroup G,
      K ∈ Chapter1.cComponentsIn (s.marking.Gi 1) ∧ s.marking.Li 1 ≤ K ∧
      (K.subgroupOf (s.marking.Gi 1)).Normal ∧ RemainingPointModel (K ⧸ pCore 2 K) := by
  obtain ⟨K,⟨hK,hLK,hN⟩,_⟩ := s.exists_unique_normal_local_component h 1 (.inl rfl)
  rcases s.point_component_alternative_or_remaining h hK hLK hN with ha | hm
  · exact .inl ⟨s.localComponentsOfPointAlternative h K hK hLK hN ha⟩
  · exact .inr ⟨K,hK,hLK,hN,hm⟩

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
