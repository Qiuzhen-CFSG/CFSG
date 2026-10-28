module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.FourFinite
/-!
# The complete degree-four point-component catalogue

Apply the original known-simple A.3.6 catalogue to the actual containing
component in G₁/O₂(G₁). The rank-one, even rank-two, odd ternary, finite
sporadic and central-cover comparisons give exactly the alternatives of
12.9.3. A nonquasisimple component has its actual elementary seven-core
and SL₂(7) quotient, without a splitting assumption.

The normal containing component is constructed with the original marking.
Its point fields feed ComponentGeometry; FourThree discharges the remaining
three-space assertion. Nonnormal point-span abelianity remains a separate
source obligation. Source: Aschbacher--Smith 12.9.3, p.858, and A.3.6,
pp.43--45. The catalogue transport follows Section05 PointCatalogue.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
  (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple) (F : InvariantFlag T V 4)
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



include h earlier in
private theorem four_point_alternative_of_simple_catalogue
    {K : Subgroup G} (hK : K ∈ Chapter1.cComponentsIn F.H) (hLK : F.Li L 1 ≤ K)
    {X : Type*} [Group X] (e : (K ⧸ pCore 2 K) ≃* X) (hm : TheoremCModel X) :
    K = F.Li L 1 ∨ LargePointModel (K ⧸ pCore 2 K) ∨ FourPointModel (K ⧸ pCore 2 K) := by
  cases hm with
  | alternating n hn hm =>
    have hn' : n = 7 ∨ n = 8 := by
      have hd := four_point_component_quotient_seven_dvd h F hLK
      rw [Nat.card_congr (e.trans hm.some).toEquiv] at hd
      obtain ⟨hn5,hn8⟩ := hn
      interval_cases n
      · rw [nat_card_alternatingGroup] at hd; norm_num at hd
      · rw [nat_card_alternatingGroup] at hd; norm_num at hd
      · exact .inl rfl
      · exact .inr rfl
    rcases hn' with rfl | rfl
    · exact .inr (.inr (.inr (.inl ⟨e.trans hm.some⟩)))
    · exact .inr (.inr (.inl ⟨ZMod 2,inferInstance,inferInstance,by simp,
        ⟨(e.trans hm.some).trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm⟩⟩))
  | linear_odd p d hp ho hd _ hm =>
    exact .inl (four_point_component_eq_of_odd_linear h earlier F hK hLK hp ho hd
      (hm.of_mulEquiv e)).symm
  | three_odd p hp ho unitary hm =>
    exact (four_point_component_not_odd_ternary h earlier F hK hLK hp ho unitary
      (.inl (pslSign_transport e hm))).elim
  | rank_one hm =>
    exact .inl (four_point_component_eq_of_bender h earlier F hK hLK (hm.of_mulEquiv e)).symm
  | rank_two hm =>
    exact .inl (four_point_component_eq_of_even_rank_two h earlier F hK hLK
      (rankTwoModel_transport e hm)).symm
  | binary_linear n hn hm =>
    rcases hn with rfl | rfl
    · exact .inr (.inr (.inl (hm.of_mulEquiv e)))
    · exact .inr (.inl (.inl (hm.of_mulEquiv e)))
  | sporadic name hj hm =>
    let a := e.trans hm.some
    cases name with
    | m11 => exact (four_point_component_not_small_mathieu h F hLK (.inl ⟨a⟩)).elim
    | m12 => exact (four_point_component_not_small_mathieu h F hLK (.inr ⟨a⟩)).elim
    | m22 => exact (four_point_component_not_mathieuTwentyTwo h earlier F hK hLK a).elim
    | m23 => exact .inr (.inr (.inr (.inr (.inr (.inl ⟨a⟩)))))
    | m24 => exact .inr (.inl (.inr (.inl ⟨a⟩)))
    | j2 => exact (four_point_component_not_jankoTwo h earlier F hK hLK a).elim
    | j3 => exact (hj rfl).elim
    | j4 => exact .inr (.inl (.inr (.inr ⟨a⟩)))
    | hs => exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨a⟩))))))
    | he => exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨a⟩)))))))
    | ru => exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨a⟩))))))))
  | janko_one hm =>
    exact (four_point_component_not_jankoOne h F hLK ⟨e.trans hm.some⟩).elim

include h earlier in
private theorem four_point_alternative_of_cover_catalogue
    {K : Subgroup G} (hK : K ∈ Chapter1.cComponentsIn F.H) (hLK : F.Li L 1 ≤ K)
    {X : Type*} [Group X] (e : (K ⧸ pCore 2 K) ≃* X) (hm : ThreeCoverModel X) :
    K = F.Li L 1 ∨ FourPointModel (K ⧸ pCore 2 K) := by
  cases hm with
  | classical unitary q hq hm =>
    have hm' := slSign_transport e hm
    rcases hq with ⟨n,hn,rfl,_⟩ | ⟨hp,ho⟩
    · exact .inl (four_point_component_eq_of_even_classical_cover h earlier F hK hLK hn unitary hm').symm
    · exact (four_point_component_not_odd_ternary h earlier F hK hLK hp ho unitary (.inr hm')).elim
  | alternating_six hm =>
    exact (four_point_component_not_alternating_six_cover h F hLK (threeCover_transport e hm)).elim
  | alternating_seven hm => exact .inr (.inr (.inr (.inl (threeCover_transport e hm))))
  | mathieu hm =>
    exact (four_point_component_not_mathieu_cover h earlier F hK hLK (threeCover_transport e hm)).elim

include h earlier in
/-- The complete degree-four point list from the actual known-simple catalogue. -/
theorem four_point_component_models
    {K : Subgroup G} (hK : K ∈ Chapter1.cComponentsIn F.H) (hLK : F.Li L 1 ≤ K) :
    K = F.Li L 1 ∨ LargePointModel (K ⧸ pCore 2 K) ∨ FourPointModel (K ⧸ pCore 2 K) := by
  by_cases hq : IsQuasisimple (K ⧸ pCore 2 K)
  · let H : Subgroup G := F.H
    let C := (K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))
    let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
    have hKC : (K.subgroupOf H).IsCComponent := hK.2
    let a := subgroupOfEquivOfLe hK.1
    let e : (K ⧸ pCore 2 K) ≃* C :=
      (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans
        (cComponentTwoCoreQuotientEquiv hKC)
    let := hq
    let : IsQuasisimple C := IsQuasisimple.of_mulEquiv e
    have hH : IsSQTK KnownSimple.IsKnownSimple H :=
      h.source.simpleQTKE.twoLocal_sqtk (Gi_twoLocal h F 1 (by decide))
    have hQ := ChapterE.Structure.sqtk_two_quotient hH (pCore 2 H) pCore_isPGroup
    rcases ChapterA.Section03.SourceEmbeddings.quasisimple_containing_component_models_knownSimple
        hQ (pCore_quotient_pCore_eq_bot 2) (hKC.map_quotient (pCore 2 H)) with ⟨_,hm⟩ | ⟨_,hm⟩
    · exact four_point_alternative_of_simple_catalogue h earlier F hK hLK e hm
    · rcases four_point_alternative_of_cover_catalogue h earlier F hK hLK e hm with he | hm
      · exact .inl he
      · exact .inr (.inr hm)
  · have hm := component_nonquasisimple_seven_core h F 1
      (Or.inr ⟨rfl,Or.inl rfl⟩) rfl hK hLK hq
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
      ⟨pCore 7 (K ⧸ pCore 2 K),inferInstance,hm⟩))))))))

include h earlier in
/-- The original normal containing point component with every source alternative. -/
theorem exists_four_point_component :
    ∃ D : Subgroup G, D ∈ Chapter1.cComponentsIn F.H ∧ F.Li L 1 ≤ D ∧
      (D.subgroupOf F.H).Normal ∧
      (D = F.Li L 1 ∨ LargePointModel (D ⧸ pCore 2 D) ∨ FourPointModel (D ⧸ pCore 2 D)) := by
  obtain ⟨D,hd,_⟩ := exists_unique_normal_local_component h earlier F 1
    (Or.inr ⟨rfl,Or.inl rfl⟩)
  exact ⟨D,hd.1,hd.2.1,hd.2.2,four_point_component_models h earlier F hd.1 hd.2.1⟩

include h earlier in
/-- The point catalogue discharges the point fields of the original ComponentGeometry.
The three-space assertion remains with this source assembly owner. -/
theorem four_componentGeometry_of_three_component
    (h3 : ((F.Li L 3).subgroupOf (F.Gi 3)).IsCComponent ∧
      ((F.Li L 3).subgroupOf (F.Gi 3)).Normal) : Nonempty (ComponentGeometry F L) := by
  obtain ⟨D,hD,hLD,hN,hm⟩ := exists_four_point_component h earlier F
  refine ⟨⟨D,hD.1,hLD,hD.2,hN,?_,?_⟩⟩
  · rcases hm with he | hm | hm
    · exact .inl he
    · exact .inr (.inl hm)
    · exact .inr (.inr ⟨rfl,hm⟩)
  · intro i hi
    rcases hi with ⟨he,_,_⟩ | ⟨_,rfl⟩
    · omega
    · exact h3

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
