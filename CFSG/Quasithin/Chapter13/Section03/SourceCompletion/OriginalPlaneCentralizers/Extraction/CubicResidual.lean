module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Extraction.SecondCubic
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Extraction.Components
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.CubicNormality

/-!
# Cubic component control in the original plane normalizer

The marked second cubic lies outside H = C_G(A), which is normal in
N_G(A). Promote each relative H-component to a component of N_G(A).
The original nonnormal-component residual theorem then makes every component
with a cubic in its two-core quotient normal in N_G(A). Its Q-normalization
constructs the actual LocalData, including the previously repositioned Sylow.

The only remaining moved-component alternative has an actual Suzuki quotient;
its escaping property and full Sylow intersection are retained. Eliminating
that alternative still requires the full-Sylow block argument of C.2.4(1).
This file does not assert LocalExtraction or the plane-centralizer theorem.

Source: Aschbacher--Smith 13.3.12, printed p.889; 1.2.1--2, pp.504--505.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open ChapterE Atlas.G2.Natural.BinaryNondegeneratePlane
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

theorem Context.plane_component_normalizes_of_three_dvd
    (s : Context T L V) (d : MarkedPlane V) {J : Subgroup G}
    (hJ : J ∈ Chapter1.cComponentsIn (centralizer (d.A : Set G)))
    [IsQuasisimple (J ⧸ pCore 2 J)]
    (hd : 3 ∣ Nat.card (J ⧸ pCore 2 J)) :
    normalizer (d.A : Set G) ≤ normalizer (J : Set G) := by
  let N := normalizer (d.A : Set G)
  let H := centralizer (d.A : Set G)
  let HN := H.subgroupOf N
  let JN := J.subgroupOf N
  have hHN : H ≤ N := Subgroup.centralizer_le_normalizer _
  have hJN : J ≤ N := hJ.1.trans hHN
  let eH : H ≃* HN := (subgroupOfEquivOfLe hHN).symm
  have hm : (J.subgroupOf H).map eH.toMonoidHom = JN.subgroupOf HN := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      exact ⟨eH.symm x,hx,eH.apply_symm_apply x⟩
  have hc : JN.IsCComponent :=
    (IsCComponent.subgroupOf_iff (inferInstance : HN.Normal).isSubnormal
      (comap_mono hJ.1)).mp (hm ▸ hJ.2.map_equiv eH)
  let eJ := subgroupOfEquivOfLe hJN
  let eQ := QuotientGroup.congr (pCore 2 JN) (pCore 2 J) eJ (pCore_map_iso 2 eJ)
  let : IsQuasisimple (JN ⧸ pCore 2 JN) := IsQuasisimple.of_mulEquiv eQ.symm
  obtain ⟨n,hn,_,hout⟩ := s.plane_cubic_escape d
  have hi : JN.Normal := Chapter1.Section02.component_normal_of_cubic_outside_normal
    (s.hypothesis.qtke.twoLocal_sqtk
      ⟨d.A,d.ne_bot,IsPGroup.of_card (n := 2) d.card,rfl⟩)
    HN hc (comap_mono hJ.1) (by rwa [Nat.card_congr eQ.toEquiv]) n hn hout
  exact (normal_subgroupOf_iff_le_normalizer hJN).mp hi

theorem Context.localData_of_component_three_dvd
    (s : Context T L V) (d : MarkedPlane V) (J : Subgroup G)
    (hJ : J ∈ Chapter1.cComponentsIn (centralizer (d.A : Set G)))
    (hq : IsQuasisimple (J ⧸ pCore 2 J))
    (hf : generalizedFitting J = pCore 2 J)
    (hout : ¬ J ≤ centralizer (d.A : Set G) ⊓ normalizer (L : Set G))
    (hd : 3 ∣ Nat.card (J ⧸ pCore 2 J)) : Nonempty (LocalData T L d J) := by
  let := hq
  apply s.localData_of_normalized_component d J hJ hq hf hout
  exact ((s.plane_local_control d).1.trans (Subgroup.centralizer_le_normalizer _)).trans
    (s.plane_component_normalizes_of_three_dvd d hJ hd)

theorem Context.localData_or_three_free_component
    (s : Context T L V) (d : MarkedPlane V)
    (hout : ¬ centralizer (d.A : Set G) ≤ normalizer (L : Set G)) :
    (∃ J : Subgroup G, Nonempty (LocalData T L d J)) ∨
      ∃ J : Subgroup G,
        J ∈ Chapter1.cComponentsIn (centralizer (d.A : Set G)) ∧
        IsQuasisimple (J ⧸ pCore 2 J) ∧ generalizedFitting J = pCore 2 J ∧
        ¬ J ≤ centralizer (d.A : Set G) ⊓ normalizer (L : Set G) ∧
        ¬ (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ normalizer (J : Set G) ∧
        (∃ S : Sylow 2 J, (S : Subgroup J).map J.subtype =
          (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ J) ∧
        ¬ 3 ∣ Nat.card (J ⧸ pCore 2 J) := by
  rcases s.localData_or_moved_component d hout with h | ⟨J,hJ,hq,hf,ho,hn,hs⟩
  · exact Or.inl h
  · by_cases hd : 3 ∣ Nat.card (J ⧸ pCore 2 J)
    · exact Or.inl ⟨J,s.localData_of_component_three_dvd d J hJ hq hf ho hd⟩
    · exact Or.inr ⟨J,hJ,hq,hf,ho,hn,hs,hd⟩

theorem Context.moved_plane_component_suzuki
    (s : Context T L V) (d : MarkedPlane V) {J : Subgroup G}
    (hJ : J ∈ Chapter1.cComponentsIn (centralizer (d.A : Set G)))
    [IsQuasisimple (J ⧸ pCore 2 J)]
    (hn : ¬ (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ normalizer (J : Set G)) :
    ∃ m, 1 ≤ m ∧
      Nonempty ((J ⧸ pCore 2 J) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  let H := centralizer (d.A : Set G)
  have hH := (s.plane_local_control d).2.1
  have hQ : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
    refine ⟨?_,hH.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 H) pCore_isPGroup).trans
      (hH.stronglyQuasithin p hp ho)
  have hnot : ¬ (J.subgroupOf H).Normal := fun hi => hn
    ((s.plane_local_control d).1.trans ((normal_subgroupOf_iff_le_normalizer hJ.1).mp hi))
  obtain ⟨_,hm⟩ := (Chapter1.Section02.proposition_1_2_1_three_index_knownSimple
    hQ hJ.2).resolve_left hnot
  let eJ := subgroupOfEquivOfLe hJ.1
  let eQ := QuotientGroup.congr _ _ eJ (pCore_map_iso 2 eJ)
  have hmJ := hm.of_mulEquiv eQ.symm
  apply hmJ.suzuki_of_three_free
  intro hd
  exact hn (((s.plane_local_control d).1.trans (Subgroup.centralizer_le_normalizer _)).trans
    (s.plane_component_normalizes_of_three_dvd d hJ hd))

theorem Context.localData_or_moved_suzuki
    (s : Context T L V) (d : MarkedPlane V)
    (hout : ¬ centralizer (d.A : Set G) ≤ normalizer (L : Set G)) :
    (∃ J : Subgroup G, Nonempty (LocalData T L d J)) ∨
      ∃ J : Subgroup G,
        J ∈ Chapter1.cComponentsIn (centralizer (d.A : Set G)) ∧
        IsQuasisimple (J ⧸ pCore 2 J) ∧ generalizedFitting J = pCore 2 J ∧
        ¬ J ≤ centralizer (d.A : Set G) ⊓ normalizer (L : Set G) ∧
        ¬ (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ normalizer (J : Set G) ∧
        (∃ S : Sylow 2 J, (S : Subgroup J).map J.subtype =
          (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ J) ∧
        ∃ m, 1 ≤ m ∧
          Nonempty ((J ⧸ pCore 2 J) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  rcases s.localData_or_moved_component d hout with h | ⟨J,hJ,hq,hf,ho,hn,hs⟩
  · exact Or.inl h
  · let := hq
    exact Or.inr ⟨J,hJ,hq,hf,ho,hn,hs,s.moved_plane_component_suzuki d hJ hn⟩

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
