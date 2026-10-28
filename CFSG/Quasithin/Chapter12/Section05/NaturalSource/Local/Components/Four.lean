module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.Rigidity
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.Containing
/-!
# The four-dimensional local component equals the original residual

The actual Lᵢ/O₂(Lᵢ) is PSL₄(2) for i = 4,6. Its image in Gᵢ/O₂(Gᵢ)
retains that section under the solvable quotient map. The earlier A₈
containing-component theorem therefore proves that Kᵢ/O₂(Kᵢ) is quasisimple.
At i = 4, the full natural action and two-core normalization force K₄ = L₄.
Applying this to the unique normal containing component gives the component
and relative normality clauses of 12.5.3 at i = 4 from Hypothesis 12.2.3.

The six-dimensional orthogonal action still requires its separate extension
exclusions; quasisimplicity alone is not the i = 6 conclusion.
Source: Aschbacher--Smith, 12.5.3, printed pp.818--819, using A.3.6/A.3.12.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

/-- The A₈ section excludes the nonquasisimple containing-component rows. -/
theorem local_linear_four_component_quasisimple
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (i : ℕ) (hi4 : i = 4 ∨ i = 6) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi i))
    (hLK : s.marking.Li i ≤ K) : IsQuasisimple (K ⧸ pCore 2 K) := by
  have hi : LocalIndex i := by rcases hi4 with rfl | rfl <;> simp [LocalIndex]
  let H := s.marking.Gi i
  let B := (s.marking.Li i).subgroupOf H
  let C := K.subgroupOf H
  have hT := s.sylow_le_Gi i hi
  let S := T.subtype hT
  let q := QuotientGroup.mk' (pCore 2 H)
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  let : Group.IsSolvable q.ker := by
    change Group.IsSolvable (QuotientGroup.mk' (pCore 2 H)).ker
    rw [QuotientGroup.ker_mk']
    infer_instance
  have hB : B ∈ Chapter1.L H S := by
    simpa only [S, B, H, Sylow.coe_subtype] using
      (Chapter1.mem_LIn_iff_subgroupOf hT (s.marking.Li_le_Gi i)).mp
        ⟨s.marking.Li_le_Gi i, s.Li_mem_local i hi⟩
  let : Group.IsPerfect B := Chapter1.mem_L_isPerfect hB
  let eB : B ≃* s.marking.Li i := subgroupOfEquivOfLe (s.marking.Li_le_Gi i)
  have hbmodel : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2 := by
    refine ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2, ⟨?_⟩⟩
    have ei : (s.marking.Li i ⧸ pCore 2 (s.marking.Li i)) ≃*
        Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) := by
      have hdim : localLinearDimension i = 4 := by
        rcases hi4 with rfl | rfl <;> simp [localLinearDimension]
      rw [← hdim]
      exact s.marking.LiCoreEquiv i hi
    exact ((QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB)).trans ei).trans
      Atlas.Order20160A8.sl4TwoEquivPSL
  have hQ := ChapterE.Structure.sqtk_two_quotient
    (h.simpleQTKE.twoLocal_sqtk (s.marking.Gi_twoLocal i hi)) (pCore 2 H) pCore_isPGroup
  have hbq : B.map q ∈ ChapterA.Section03.localCComponents
      (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))) := by
    simpa only [Sylow.coe_mapSurjective] using
      Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hB
  let : IsQuasisimple (C.map q) :=
    ChapterA.Section03.SourceEmbeddings.AlternatingEight.containing_quasisimple
      hQ (pCore_quotient_pCore_eq_bot 2)
      (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))) hbq
      (hK.2.map_quotient _) (map_mono (comap_mono hLK))
      (ChapterA.Section03.SourceEmbeddings.AlternatingEight.section_map B hbmodel q)
  let eC : C ≃* K := subgroupOfEquivOfLe hK.1
  exact IsQuasisimple.of_mulEquiv
    ((cComponentTwoCoreQuotientEquiv hK.2).symm.trans
      (QuotientGroup.congr _ _ eC (pCore_map_iso 2 eC)))

/-- Every containing local C-component at the four-space is exactly L₄. -/
theorem local_four_component_eq
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 4))
    (hLK : s.marking.Li 4 ≤ K) : s.marking.Li 4 = K := by
  let := s.local_linear_four_component_quasisimple h 4 (Or.inl rfl) hK hLK
  exact s.local_component_eq_of_quasisimple 4 (Or.inr rfl) hK hLK

/-- The i = 4 component and relative normality conclusion of source 12.5.3. -/
theorem local_four_component_source
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    s.marking.Li 4 ∈ Chapter1.cComponentsIn (s.marking.Gi 4) ∧
      ((s.marking.Li 4).subgroupOf (s.marking.Gi 4)).Normal := by
  obtain ⟨K, ⟨hK, hLK, hn⟩, _⟩ := s.exists_unique_normal_local_component h 4
    (Or.inr (Or.inr (Or.inl rfl)))
  exact (s.local_four_component_eq h hK hLK).symm ▸ ⟨hK, hn⟩
end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
