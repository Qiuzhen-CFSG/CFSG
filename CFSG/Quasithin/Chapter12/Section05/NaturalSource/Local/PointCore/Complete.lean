module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.LowRank
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.MathieuCover
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.PointModels
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.PointEvenRankTwo
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.PointSporadicComplete
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.PointNonenlargement
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.QuasisimpleContaining

/-!
# Source point-core containment without a component-refinement premise

Construct the normal containing component from the original exterior marking
and Hypothesis1223. Its nonquasisimple quotient is the proved radical row.
For a quasisimple quotient, apply the complete A.3.6 catalogue to its actual
image in G₁/O₂(G₁). The existing simple-model arguments, the direct low-rank
argument for odd ternary and alternating covers, and the Mathieu22-cover
argument settle every row, proving V ≤ O₂(G₁).

The original component and quotient maps are retained throughout. This
completes 12.5.8(1); it does not construct LocalComponents or prove the general
G₃,G₆ normalizer containments. Those and the remaining strict-enlargement
argument remain with qt-d-1251-local. PointCore.Source supplies the original
consumers; qt-d-1251-source retains final exterior assembly.
Source: Aschbacher--Smith 12.5.8(1), printed p.820, using A.3.6 and 1.2.4.
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

private theorem seed_le_point_core_of_simple_catalogue
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    {X : Type*} [Group X] (e : (K ⧸ pCore 2 K) ≃* X)
    (hm : TheoremCModel X) : V ≤ (s.marking.Gi 1).pCoreIn 2 := by
  cases hm with
  | alternating n hn hm =>
    exact (s.point_component_not_alternating h hK hLK hN hn
      (hm.map fun a => e.trans a)).elim
  | linear_odd p d hp ho hd _ hm =>
    exact (s.local_containments_of_non_enlarging_point_model h hK hLK hN
      (.inr (.inr (.inl ⟨p,d,hp,ho,hd,hm.of_mulEquiv e⟩)))).2.2
  | three_odd p hp ho unitary hm =>
    exact s.seed_le_point_core_of_odd_ternary hLK hK.1 hN hp ho unitary
      (.inl (pslSign_transport e hm))
  | rank_one hm =>
    exact (s.local_containments_of_non_enlarging_point_model h hK hLK hN
      (.inl (hm.of_mulEquiv e))).2.2
  | rank_two hm =>
    exact (s.local_containments_of_even_rank_two_point_model h hK hLK hN
      (rankTwoModel_transport e hm)).2.2
  | binary_linear n hn hm =>
    exact s.seed_le_point_core_of_binary_linear_point_model h hK hLK hN hn (hm.of_mulEquiv e)
  | sporadic name hj hm =>
    exact s.seed_le_point_core_of_sporadic_point_model h hK hLK hN
      (.inl ⟨name,hj,hm.map fun a => e.trans a⟩)
  | janko_one hm =>
    exact s.seed_le_point_core_of_sporadic_point_model h hK hLK hN
      (.inr (hm.map fun a => e.trans a))

private theorem seed_le_point_core_of_cover_catalogue
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    {X : Type*} [Group X] (e : (K ⧸ pCore 2 K) ≃* X)
    (hm : ThreeCoverModel X) : V ≤ (s.marking.Gi 1).pCoreIn 2 := by
  cases hm with
  | classical unitary q hq hm =>
    have hm' := slSign_transport e hm
    rcases hq with ⟨n,hn,rfl,_⟩ | ⟨hp,ho⟩
    · exact (s.local_containments_of_even_classical_cover_point_model h hK hLK hN
        hn unitary hm').2.2
    · exact s.seed_le_point_core_of_odd_ternary hLK hK.1 hN hp ho unitary (.inr hm')
  | alternating_six hm =>
    exact s.seed_le_point_core_of_small_alternating_cover hLK hK.1 hN (by decide)
      (threeCover_transport e hm)
  | alternating_seven hm =>
    exact s.seed_le_point_core_of_small_alternating_cover hLK hK.1 hN (by decide)
      (threeCover_transport e hm)
  | mathieu hm =>
    exact s.seed_le_point_core_of_mathieu_cover hLK hK.1 hN (threeCover_transport e hm)

/-- Point-core containment from the complete catalogue of the actual normal component. -/
theorem seed_le_point_core_of_normal_containing_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal) :
    V ≤ (s.marking.Gi 1).pCoreIn 2 := by
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
    · exact s.seed_le_point_core_of_simple_catalogue h hK hLK hN e hm
    · exact s.seed_le_point_core_of_cover_catalogue h hK hLK hN e hm
  · exact s.seed_le_point_core_of_nonquasisimple_component h hK hLK hN hq

/-- Source 12.5.8(1), without a LocalComponents premise. -/
theorem seed_le_point_core_from_source
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    V ≤ (s.marking.Gi 1).pCoreIn 2 := by
  obtain ⟨K,⟨hK,hLK,hN⟩,_⟩ := s.exists_unique_normal_local_component h 1 (.inl rfl)
  exact s.seed_le_point_core_of_normal_containing_component h hK hLK hN

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
