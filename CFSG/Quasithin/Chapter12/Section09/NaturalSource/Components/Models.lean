module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.Membership
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.Abelian
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.Catalogue

/-!
# Point and hyperplane components in degree five

The literal end-node residual has PSL₄(2) two-core quotient. The proved
restricted A.3.12 catalogue therefore gives the actual point component
and its three possible strict enlargements: PSL₅(2), M₂₄, and J₄.
Its two-core quotient is quasisimple even before that catalogue is applied.
At the hyperplane, full action and component rigidity force K₄=L₄.

The final theorem applies these results to the unchanged ComponentGeometry
record, leaving only the two middle-index identifications explicit for
qt-d-1291-natural-source. The nonabelian point-span theorem constructs the
actual strict overcomponent; it does not eliminate those remaining models.

Source: Aschbacher--Smith,12.9.3 and the opening of12.9.4,
printed pp.858--859 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag
open BinaryLinear.OuterCyclic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ}

/-- The source linear model has the exact larger block degree. -/
theorem Li_core_model {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (F : InvariantFlag T V n)
    (i : ℕ) (hi : ComponentIndex n i) :
    ClassicalGroup.IsPSL (F.Li L i ⧸ pCore 2 (F.Li L i)) (max i (n-i)) 2 := by
  let := h.chosen.elementary
  obtain ⟨d,hd,hd',⟨e⟩⟩ := Li_core_linear F h.naturalMarking i hi
  subst d
  refine ⟨ZMod 2,inferInstance,inferInstance,by simp,?_⟩
  exact ⟨e.trans (projectiveEquivLinear (by omega)).symm⟩

/-- For either end node at n=5, the containing component is unchanged or
has one of the three larger source quotients. -/
theorem five_endpoint_component_models
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) (i : ℕ) (hi : i = 1 ∨ i = 4)
    (D : Subgroup G) (hD : D ∈ Chapter1.cComponentsIn (F.Gi i))
    (hLD : F.Li L i ≤ D) : D = F.Li L i ∨ LargePointModel (D ⧸ pCore 2 D) := by
  have hidx : ComponentIndex 5 i := Or.inl ⟨rfl,by omega,by omega⟩
  have hT : (T : Subgroup G) ≤ F.Gi i := F.invariant i
  have hL : F.Li L i ≤ F.Gi i := (F.Li_le L i).trans inf_le_right
  have hl : (F.Li L i).subgroupOf (F.Gi i) ∈ Chapter1.L (F.Gi i) (T.subtype hT) := by
    simpa only [Sylow.coe_subtype] using
      (Chapter1.mem_LIn_iff_subgroupOf hT hL).mp ⟨hL,Li_mem_local h earlier F i hidx⟩
  have hn : (T.subtype hT : Subgroup (F.Gi i)) ≤
      normalizer ((F.Li L i).subgroupOf (F.Gi i) : Set (F.Gi i)) := by
    intro t ht b
    exact sylow_normalizes_Li h earlier F i ht (b : G)
  have hm : ClassicalGroup.IsPSL (F.Li L i ⧸ pCore 2 (F.Li L i)) 4 2 := by
    have he : max i (5-i) = 4 := by omega
    simpa only [he] using Li_core_model h F i hidx
  let eL := subgroupOfEquivOfLe hL
  have hmodel := hm.of_mulEquiv (QuotientGroup.congr _ _ eL (pCore_map_iso 2 eL))
  have hmodels := ChapterA.Section03.SourceEmbeddings.AlternatingEight.restricted_containing_models
    (h.source.simpleQTKE.twoLocal_sqtk (Gi_twoLocal h F i (by omega)))
    (T.subtype hT) hl.1 hD.2 (comap_mono hLD) hn hmodel
  let eD := subgroupOfEquivOfLe hD.1
  let eQ := QuotientGroup.congr _ _ eD (pCore_map_iso 2 eD)
  rcases hmodels with he | hm | hm | hm
  · left
    exact ((map_subgroupOf_eq_of_le hD.1).symm.trans
      ((congrArg (map (F.Gi i).subtype) he.symm).trans (map_subgroupOf_eq_of_le hL)))
  · exact Or.inr (Or.inl (hm.of_mulEquiv eQ.symm))
  · exact Or.inr (Or.inr (Or.inl ⟨eQ.symm.trans hm.some⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨eQ.symm.trans hm.some⟩))

/-- The n=5 point component, with its actual normality and complete quotient
alternatives. This is the point-index case of 12.9.3. -/
theorem exists_five_point_component
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) :
    ∃ D : Subgroup G, D ∈ Chapter1.cComponentsIn F.H ∧ F.Li L 1 ≤ D ∧
      (D.subgroupOf F.H).Normal ∧
      (D = F.Li L 1 ∨ LargePointModel (D ⧸ pCore 2 D)) := by
  obtain ⟨D,hd,_⟩ := exists_unique_normal_local_component h earlier F 1
    (Or.inl ⟨rfl,by decide,by decide⟩)
  exact ⟨D,hd.1,hd.2.1,hd.2.2,
    five_endpoint_component_models h earlier F 1 (Or.inl rfl) D hd.1 hd.2.1⟩

/-- The surviving n=5 nonabelian branch has a proper containing point
component with one of the larger quotients. This applies the normal-L₁
exclusion to the component actually constructed above. -/
theorem exists_nonabelian_five_point_component
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) (hne : ¬ IsMulCommutative F.U) :
    ∃ D : Subgroup G, D ∈ Chapter1.cComponentsIn F.H ∧ F.Li L 1 < D ∧
      (D.subgroupOf F.H).Normal ∧ LargePointModel (D ⧸ pCore 2 D) := by
  obtain ⟨D,hD,hLD,hn,hm⟩ := exists_five_point_component h earlier F
  have hlt := point_residual_lt_of_nonabelian h (Or.inr rfl) earlier F hne D hLD hn
  refine ⟨D,hD,hlt,hn,?_⟩
  exact hm.resolve_left (fun he => hlt.ne he.symm)

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components

namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Quasisimplicity of the actual two-core quotient at either end node
in degree five, before applying the larger-model catalogue. -/
theorem five_endpoint_component_quasisimple
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) (i : ℕ) (hi : i = 1 ∨ i = 4)
    (D : Subgroup G) (hD : D ∈ Chapter1.cComponentsIn (F.Gi i))
    (hLD : F.Li L i ≤ D) : IsQuasisimple (D ⧸ pCore 2 D) := by
  let H := F.Gi i
  let B := (F.Li L i).subgroupOf H
  let C := D.subgroupOf H
  let N := pCore 2 H
  let q := QuotientGroup.mk' N
  have hT : (T : Subgroup G) ≤ H := F.invariant i
  have hL : F.Li L i ≤ H := (F.Li_le L i).trans inf_le_right
  have hl : B ∈ Chapter1.L H (T.subtype hT) := by
    simpa only [Sylow.coe_subtype] using
      (Chapter1.mem_LIn_iff_subgroupOf hT hL).mp
        ⟨hL,Li_mem_local h earlier F i (Or.inl ⟨rfl,by omega,by omega⟩)⟩
  have hn : (T.subtype hT : Subgroup H) ≤ normalizer (B : Set H) := by
    intro t ht b
    exact sylow_normalizes_Li h earlier F i ht (b : G)
  have hm : ClassicalGroup.IsPSL (F.Li L i ⧸ pCore 2 (F.Li L i)) 4 2 := by
    have he : max i (5-i) = 4 := by omega
    simpa only [he] using Li_core_model h F i (Or.inl ⟨rfl,by omega,by omega⟩)
  let eL := subgroupOfEquivOfLe hL
  have hb := hm.of_mulEquiv (QuotientGroup.congr _ _ eL (pCore_map_iso 2 eL))
  have hH := h.source.simpleQTKE.twoLocal_sqtk (Gi_twoLocal h F i (by omega))
  have hQ := ChapterE.Structure.sqtk_two_quotient hH N pCore_isPGroup
  let : Group.IsNilpotent N := pCore_isNilpotent
  let : Group.IsSolvable q.ker := by
    change Group.IsSolvable (QuotientGroup.mk' N).ker
    rw [QuotientGroup.ker_mk']
    infer_instance
  obtain ⟨hl',_,hb'⟩ := ChapterA.Section03.SourceEmbeddings.AlternatingEight.local_section_map
    hl.1 hn hb q
  let S := (T.subtype hT).mapSurjective (QuotientGroup.mk'_surjective N)
  let : IsQuasisimple (C.map q) :=
    ChapterA.Section03.SourceEmbeddings.AlternatingEight.containing_quasisimple
      hQ (pCore_quotient_pCore_eq_bot 2) S hl' (hD.2.map_quotient N)
      (map_mono (comap_mono hLD)) hb'
  let eC := subgroupOfEquivOfLe hD.1
  let eQ := QuotientGroup.congr _ _ eC (pCore_map_iso 2 eC)
  let e := cComponentTwoCoreQuotientEquiv hD.2
  exact IsQuasisimple.of_mulEquiv (e.symm.trans eQ)

/-- The hyperplane component in degree five is L₄ itself, with normality
inside the literal N_G(V₄). This discharges the i=4 branch of 12.9.3. -/
theorem five_hyperplane_component
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) :
    ((F.Li L 4).subgroupOf (F.Gi 4)).IsCComponent ∧
      ((F.Li L 4).subgroupOf (F.Gi 4)).Normal := by
  let := h.chosen.elementary
  obtain ⟨D,hd,_⟩ := exists_unique_normal_local_component h earlier F 4
    (Or.inl ⟨rfl,by decide,by decide⟩)
  have hq := five_endpoint_component_quasisimple h earlier F 4 (Or.inr rfl) D hd.1 hd.2.1
  have he := component_eq_of_quasisimple h earlier F 4 (by decide) (by decide)
    D hd.1 hd.2.1 hd.2.2 hq
  exact he ▸ ⟨hd.1.2,hd.2.2⟩
end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components

namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Actual ComponentGeometry consumer in degree five. The point-component
construction and i=4 assertion are discharged here; the two middle-index
identifications remain with the Section09 natural-source owner. -/
theorem five_componentGeometry_of_middle_components
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5)
    (hmiddle : ∀ i, i = 2 ∨ i = 3 →
      ((F.Li L i).subgroupOf (F.Gi i)).IsCComponent ∧
        ((F.Li L i).subgroupOf (F.Gi i)).Normal) : Nonempty (ComponentGeometry F L) := by
  obtain ⟨D,hD,hLD,hn,hm⟩ := exists_five_point_component h earlier F
  refine ⟨⟨D, hD.1, hLD, hD.2, hn, ?_, ?_⟩⟩
  · rcases hm with he | hm
    · exact Or.inl he
    · exact Or.inr (Or.inl hm)
  · intro i hi
    have hi' : i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases hi' with rfl | rfl | rfl
    · exact hmiddle 2 (Or.inl rfl)
    · exact hmiddle 3 (Or.inr rfl)
    · exact five_hyperplane_component h earlier F
end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
