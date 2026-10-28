module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.JankoNativeParabolic
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.PointParabolicActors

/-!
# The original actor in the same native Mathieu local

Suppose the supplied point-component map places both the original point
parabolic and the original projected actor in the specified max1 subgroup.
The parabolic is the full preimage of a Mathieu trio stabilizer. Its original
Y-image is a non-two normal seed; the actual source keeps its conjugate
closure by that actor inside the parabolic. The native Mathieu projection
preserves the seed obstruction through its whole elementary kernel and
forces the actor into the same parabolic.

The literal point-core lift then proves G_i ≤ N_G(L) for i = 3 or 6.
No actor or Sylow is replaced, and the generation exclusion is not used.
The simultaneous max1 containments remain explicit. Establishing the
relative positions of independently covered parabolic and actor, including
the max1/trio-to-max4 comparison and remaining P_i markings, stays with
qt-d-1251-local. Final exterior assembly remains with qt-d-1251-source.
Source: Aschbacher–Smith 12.5.4, printed p.819/PDF p.836.
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

/-- When the original parabolic and actor lie in the same native max1,
the actual projected Y-closure forces the actor into that parabolic. -/
theorem point_projection_le_parabolic_of_janko_same_max1
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (e : s.pointCoreImage K ≃* Janko4.Model)
    (hplace : (s.pointComponentParabolic K).map e.toMonoidHom ≤
      Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four)
    (i : ℕ) (hi : i = 3 ∨ i = 6)
    (hactor : ((s.localPointProjection K i).subgroupOf (s.pointCoreImage K)).map
      e.toMonoidHom ≤
      Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four) :
    s.localPointProjection K i ≤ s.pointCoreImage (s.marking.Mi 1) := by
  have hYK := s.Y_le_point_component_of_large_model h hK hN
    (.inr (.inr ⟨(s.pointComponentCoreEquivImage hK.1 hN).trans e⟩))
  let C := s.pointCoreImage K
  let Y := (s.pointCoreImage s.Y).subgroupOf C
  let A := (s.localPointProjection K i).subgroupOf C
  let P := s.pointComponentParabolic K
  let M := Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four
  let U := Y.map e.toMonoidHom
  let Ae := A.map e.toMonoidHom
  let H := P.map e.toMonoidHom
  have hYC : s.pointCoreImage s.Y ≤ C := s.pointCoreImage_mono hYK
  have hYP : Y ≤ P := comap_mono (s.pointCoreImage_mono
    ((map_subtype_le _).trans s.P_le_M₁))
  have hPN : P ≤ normalizer (Y : Set C) := by
    intro p hp y
    exact s.pointCoreImage_M₁_normalizes_Y hp
      (y : s.marking.Gi 1 ⧸ pCore 2 (s.marking.Gi 1))
  have hYnot : ¬ IsPGroup 2 Y := fun ht => s.pointCoreImage_Y_not_two
    (ht.of_equiv (subgroupOfEquivOfLe hYC))
  have hUnot : ¬ IsPGroup 2 U := fun ht =>
    hYnot (ht.of_equiv (e.subgroupMap Y).symm)
  have hc : conjugateSpanBy Y A ≤ P := by
    have hh : (conjugateSpanBy Y A).map C.subtype ≤ s.pointCoreImage (s.marking.Mi 1) := by
      rw [map_conjugateSpanBy, map_subgroupOf_eq_of_le hYC,
        map_subgroupOf_eq_of_le (show s.localPointProjection K i ≤ C from inf_le_left)]
      exact (s.projected_Y_span_le_point_parabolic h hN hYK i hi).trans inf_le_left
    exact map_le_iff_le_comap.mp hh
  have hUH : U ≤ H := map_mono hYP
  have hUM : U ≤ M := hUH.trans hplace
  have hHU : H ≤ normalizer (U : Set Janko4.Model) :=
    (map_mono hPN).trans (Y.le_normalizer_map e.toMonoidHom)
  have hspan : conjugateSpanBy U Ae ≤ H := by
    rw [← map_conjugateSpanBy]
    exact map_mono hc
  obtain ⟨g, hg⟩ := s.pointComponentParabolic_janko_max1 h hK hLK hN e hplace
  have hJ : H.subgroupOf M =
      (Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.trioStabilizer
        Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.standardTrio).comap
        ((MulAut.conj g).toMonoidHom.comp Janko4.LocalStructure.MathieuHallActors.projection) := by
    change ((s.pointComponentParabolic K).map e.toMonoidHom).comap M.subtype = _
    rw [hg]
    exact comap_map_eq_self_of_injective M.subtype_injective _
  have hnormal : H.subgroupOf M ≤ normalizer (U.subgroupOf M : Set M) := by
    intro p hp u
    exact hHU hp (u : Janko4.Model)
  have hnot : ¬ IsPGroup 2 (U.subgroupOf M) := fun ht =>
    hUnot (ht.of_equiv (subgroupOfEquivOfLe hUM))
  have hspanM : conjugateSpanBy (U.subgroupOf M) (Ae.subgroupOf M) ≤ H.subgroupOf M := by
    apply map_le_iff_le_comap.mp
    rw [map_conjugateSpanBy, map_subgroupOf_eq_of_le hUM, map_subgroupOf_eq_of_le hactor]
    exact hspan
  have hAeM := Janko4.LocalStructure.MathieuParabolic.actor_le_of_trio_preimage
    (H.subgroupOf M) (U.subgroupOf M) (Ae.subgroupOf M) ⟨g, hJ⟩
    (comap_mono hUH) hnormal hnot hspanM
  have hAeH : Ae ≤ H := by
    intro b hb
    exact hAeM (show (⟨b, hactor hb⟩ : M) ∈ Ae.subgroupOf M from hb)
  have hAP : A ≤ P := by
    intro a ha
    obtain ⟨p, hp, he⟩ := hAeH (mem_map_of_mem e.toMonoidHom ha)
    exact e.injective he ▸ hp
  intro a ha
  exact hAP (show (⟨a, ha.1⟩ : C) ∈ A from ha)

/-- The same-native-max1 actor branch supplies the original ambient normalizer
containment through the whole point-core quotient. -/
theorem local_normalizer_le_M_of_janko_same_max1
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (e : s.pointCoreImage K ≃* Janko4.Model)
    (hplace : (s.pointComponentParabolic K).map e.toMonoidHom ≤
      Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four)
    (i : ℕ) (hi : i = 3 ∨ i = 6)
    (hactor : ((s.localPointProjection K i).subgroupOf (s.pointCoreImage K)).map
      e.toMonoidHom ≤
      Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four) :
    s.marking.Gi i ≤ s.marking.M := by
  apply (s.local_normalizer_iff_large_point_projection h hK hLK hN
    (.inr (.inr ⟨(s.pointComponentCoreEquivImage hK.1 hN).trans e⟩)) i hi).mpr
  exact (s.point_projection_le_parabolic_of_janko_same_max1 h hK hLK hN e hplace i hi hactor).trans
    ((s.pointCoreImage_normalizes_point_iff (s.marking.Mi 1) inf_le_right).mpr
      (s.Mi_normalizes_Li 1))

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
