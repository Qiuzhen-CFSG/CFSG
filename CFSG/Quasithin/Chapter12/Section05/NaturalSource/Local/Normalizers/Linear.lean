module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.Projection
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.LargeEscape
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.NormalizerControl
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# The linear point row of the two ambient normalizer containments

The original Y = O²(P) remains a non-two-group in G₁/O₂(G₁) and is
normal in the original point parabolic. In the L₅(2) component row the
literal component intersection is a middle flag stabilizer. Its minimal,
self-centralizing radical lies in Y*. The normal closure of Y* under the
projected local actor stays in that same parabolic, so geometric radical
control puts the actor there too. The existing quotient lift then proves
G₃,G₆ ≤ N_G(L), independently of the generation-one exclusion.

These containments feed the original point-core and strict-enlargement
consumers. The latter retains only Structural1222At, whose source producer
is qt-d-1222-source. The radical and two sporadic normalizer rows remain
with qt-d-1251-local; final exterior assembly belongs to qt-d-1251-source.
All component, quotient, Sylow and original diagonal-block markings are
preserved. Source: Aschbacher--Smith, 12.5.4 and 12.5.11(2), pp.819,821.
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

omit [Finite G] in
private theorem pointCoreImage_normalizes_of_normalizes {A B : Subgroup G}
    (hn : A ≤ normalizer (B : Set G)) :
    s.pointCoreImage A ≤ normalizer (s.pointCoreImage B : Set _) := by
  let H := s.marking.Gi 1
  let q := QuotientGroup.mk' (pCore 2 H)
  have hh : A.subgroupOf H ≤ normalizer (B.subgroupOf H : Set H) := by
    intro a ha b
    exact hn ha (b : G)
  exact (map_mono hh).trans ((B.subgroupOf H).le_normalizer_map q)

/-- The original two-residual remains a non-two-group in the literal star quotient. -/
theorem pointCoreImage_Y_not_two : ¬ IsPGroup 2 (s.pointCoreImage s.Y) := by
  intro hp
  have hy : s.Y ≤ s.marking.Gi 1 := (map_subtype_le _).trans (s.P_le_M₁.trans inf_le_right)
  let f := s.pointCoreImageHom s.Y hy
  have ht : IsPGroup 2 (⊤ : Subgroup s.Y) := by
    have hh := (hp.to_subgroup ⊤).comap_of_ker_isPGroup f
      (s.pointCoreImageHom_ker_isPGroup s.Y hy)
    rw [Subgroup.comap_top] at hh
    exact hh
  have hY : IsPGroup 2 s.Y := ht.of_equiv (Subgroup.topEquiv)
  have hh := (isPPerfect_embedded_pResidual 2 s.P).hom_eq_one_of_isPGroup hY (MonoidHom.id s.Y)
  apply s.Y_not_le_point_residual
  intro y hy
  have he : (⟨y,hy⟩ : s.Y) = 1 := DFunLike.congr_fun hh ⟨y,hy⟩
  have heG : y = 1 := congrArg s.Y.subtype he
  exact heG ▸ (s.marking.Li 1).one_mem

/-- The original point parabolic normalizes the original residual image. -/
theorem pointCoreImage_M₁_normalizes_Y :
    s.pointCoreImage (s.marking.Mi 1) ≤ normalizer (s.pointCoreImage s.Y : Set _) :=
  s.pointCoreImage_normalizes_of_normalizes
    ((normal_subgroupOf_iff_le_normalizer
      ((map_subtype_le _).trans s.P_le_M₁)).mp s.Y_normal_in_M₁)

/-- In the linear point row the projected actors are contained in the original point parabolic. -/
theorem point_projection_le_parabolic_of_linear
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 5 2)
    (i : ℕ) (hi : i = 3 ∨ i = 6) :
    s.localPointProjection K i ≤ s.pointCoreImage (s.marking.Mi 1) := by
  have hYK := s.Y_le_point_component_of_large_model h hK hN (.inl hm)
  obtain ⟨e,b,he⟩ := s.pointComponentParabolic_linear_flag hK.1 hN hLK hYK hm
  let C := s.pointCoreImage K
  let Y := (s.pointCoreImage s.Y).subgroupOf C
  let A := (s.localPointProjection K i).subgroupOf C
  let P := s.pointComponentParabolic K
  have hYC : s.pointCoreImage s.Y ≤ C := s.pointCoreImage_mono hYK
  have hYP : Y ≤ P := comap_mono (s.pointCoreImage_mono
    ((map_subtype_le _).trans s.P_le_M₁))
  have hPN : P ≤ normalizer (Y : Set C) := by
    intro p hp y
    exact s.pointCoreImage_M₁_normalizes_Y hp (y : s.marking.Gi 1 ⧸ pCore 2 (s.marking.Gi 1))
  have hYnot : ¬ IsPGroup 2 Y := fun ht => s.pointCoreImage_Y_not_two
    (ht.of_equiv (subgroupOfEquivOfLe hYC))
  have hc : conjugateSpanBy Y A ≤ P := by
    have hh : (conjugateSpanBy Y A).map C.subtype ≤ s.pointCoreImage (s.marking.Mi 1) := by
      rw [map_conjugateSpanBy,map_subgroupOf_eq_of_le hYC,
        map_subgroupOf_eq_of_le (show s.localPointProjection K i ≤ C from inf_le_left)]
      exact (s.projected_Y_span_le_point_parabolic h hN hYK i hi).trans inf_le_left
    exact map_le_iff_le_comap.mp hh
  have heYP : Y.map e.toMonoidHom ≤ P.map e.toMonoidHom := map_mono hYP
  have hePN : P.map e.toMonoidHom ≤ normalizer (Y.map e.toMonoidHom : Set _) :=
    (map_mono hPN).trans (Y.le_normalizer_map e.toMonoidHom)
  have heYnot : ¬ IsPGroup 2 (Y.map e.toMonoidHom) := fun ht =>
    hYnot (ht.of_equiv (e.subgroupMap Y).symm)
  have hec : conjugateSpanBy (Y.map e.toMonoidHom) (A.map e.toMonoidHom) ≤ P.map e.toMonoidHom := by
    rw [←map_conjugateSpanBy]
    exact map_mono hc
  have hAP : A.map e.toMonoidHom ≤ P.map e.toMonoidHom := by
    rcases he with he | he
    all_goals
      change P.map e.toMonoidHom = _ at he
      rw [he] at heYP hePN hec ⊢
      exact BinaryLinear.FiveFlagGeometry.middle_actor_le_of_seed_closure b _
        (by first | exact .inl rfl | exact .inr rfl) _ _ heYP
        ((normal_subgroupOf_iff_le_normalizer heYP).mpr hePN) heYnot hec
  have hh : A ≤ P := by
    intro a ha
    obtain ⟨p,hp,he⟩ := hAP (mem_map_of_mem e.toMonoidHom ha)
    exact e.injective he ▸ hp
  intro a ha
  exact hh (show (⟨a,ha.1⟩ : C) ∈ A from ha)

/-- Both ambient normalizer containments in the L₅(2) point-component row,
independently of the generation-one exclusion. -/
theorem local_normalizers_le_M_of_linear_point_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 5 2) :
    s.marking.Gi 3 ≤ s.marking.M ∧ s.marking.Gi 6 ≤ s.marking.M := by
  have step (i : ℕ) (hi : i = 3 ∨ i = 6) : s.marking.Gi i ≤ s.marking.M := by
    apply (s.local_normalizer_iff_large_point_projection h hK hLK hN (.inl hm) i hi).mpr
    exact (s.point_projection_le_parabolic_of_linear h hK hLK hN hm i hi).trans
      (s.pointCoreImage_normalizes_of_normalizes (s.Mi_normalizes_Li 1))
  exact ⟨step 3 (.inl rfl),step 6 (.inr rfl)⟩


/-- The linear row supplies every local containment in the original source setup. -/
theorem local_containments_of_linear_point_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 5 2) :
    s.marking.Gi 3 ≤ s.marking.M ∧ s.marking.Gi 6 ≤ s.marking.M ∧
      V ≤ (s.marking.Gi 1).pCoreIn 2 := by
  obtain ⟨h3,h6⟩ := s.local_normalizers_le_M_of_linear_point_component h hK hLK hN hm
  exact ⟨h3,h6,s.seed_le_point_core_from_source h⟩

/-- Source 12.5.11(2) in the linear point row with both normalizer premises
discharged independently. Only the earlier structural source input remains. -/
theorem point_component_eq_of_linear_from_source
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    {K : Subgroup G} (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 5 2) : s.marking.Li 1 = K := by
  obtain ⟨h3,h6⟩ := s.local_normalizers_le_M_of_linear_point_component h hK hLK hN hm
  exact s.point_component_eq_of_linear_of_source_parameters h structural h3 h6 hK hLK hN hm

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
