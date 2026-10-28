module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.Linear
public import Theory.Mathieu.M24.LocalGeometry.TrioNormalizerControl

/-!
# The Mathieu point row of the two ambient normalizer containments

The original point-parabolic intersection has nontrivial two-core and
Sylow index 63. Its literal image in the native M₂₄ is therefore a trio
stabilizer. The image of Y = O²(P) is normal there and is not a two-group.
The native trio core controls actors whose conjugate closure of this seed
stays in that same parabolic. Applied to the actual point-component
projections, this proves G₃,G₆ ≤ N_G(L), independently of the generation-one
exclusion. The existing quotient lift retains the whole point-core kernel.

The strict-enlargement consumer now retains only Structural1222At, whose
source producer is qt-d-1222-source. The radical and J₄ normalizer rows
remain with qt-d-1251-local; final exterior assembly is qt-d-1251-source.
Source: Aschbacher--Smith, 12.5.3--4 and 12.5.11(2), pp.818--819,821.
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

/-- The original point-parabolic intersection is a native trio stabilizer,
with the isomorphism defined on the actual component image in G₁/O₂(G₁). -/
theorem pointComponentParabolic_mathieu_trio {K : Subgroup G}
    (hK : K ≤ s.marking.Gi 1) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hLK : s.marking.Li 1 ≤ K) (hY : s.Y ≤ K)
    (hm : Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24)) :
    ∃ e : s.pointCoreImage K ≃* Sporadic.Mathieu.M24,
      (s.pointComponentParabolic K).map e.toMonoidHom =
        Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.trioStabilizer
          Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.standardTrio := by
  obtain ⟨S,hS,hi⟩ := s.pointComponentParabolic_sylow_index hK hN hLK hY
  let a := (s.pointComponentCoreEquivImage hK hN).symm.trans hm.some
  let R := S.mapSurjective (f := a.toMonoidHom) a.surjective
  let J := (s.pointComponentParabolic K).map a.toMonoidHom
  have hSJ : (R : Subgroup Sporadic.Mathieu.M24) ≤ J := map_mono hS
  have hidx : (R : Subgroup Sporadic.Mathieu.M24).relIndex J = 63 := by
    change ((S : Subgroup _).map a.toMonoidHom).relIndex
      ((s.pointComponentParabolic K).map a.toMonoidHom) = 63
    rw [relIndex_map_map_of_injective _ _ a.injective]
    exact hi
  have h32S : 32 ∣ Nat.card S := by
    apply S.pow_dvd_card_of_pow_dvd_card (n := 5)
    rw [Nat.card_congr a.toEquiv,Sporadic.Mathieu.m24_order]
    decide
  have hc := s.pointComponentParabolic_core_ne_bot S hS h32S
  have hcJ : pCore 2 J ≠ ⊥ := by
    intro he
    let b := a.subgroupMap (s.pointComponentParabolic K)
    have hb := pCore_map_iso 2 b
    change (pCore 2 (s.pointComponentParabolic K)).map b.toMonoidHom = pCore 2 J at hb
    rw [he] at hb
    exact hc ((map_eq_bot_iff_of_injective _ b.injective).mp hb)
  obtain ⟨g,hg⟩ := Sporadic.Mathieu.M24LocalGeometry.TrioRecognition.exists_conjugate_trio
    R J hSJ hcJ hidx
  refine ⟨a.trans (MulAut.conj g),?_⟩
  change (s.pointComponentParabolic K).map
    ((MulAut.conj g).toMonoidHom.comp a.toMonoidHom) = _
  rw [←map_map]
  exact hg

/-- In the Mathieu point row the projected actors are contained in the original point parabolic. -/
theorem point_projection_le_parabolic_of_mathieu
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hm : Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24))
    (i : ℕ) (hi : i = 3 ∨ i = 6) :
    s.localPointProjection K i ≤ s.pointCoreImage (s.marking.Mi 1) := by
  have hYK := s.Y_le_point_component_of_large_model h hK hN (.inr (.inl hm))
  obtain ⟨e,he⟩ := s.pointComponentParabolic_mathieu_trio hK.1 hN hLK hYK hm
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
    change P.map e.toMonoidHom = _ at he
    rw [he] at heYP hePN hec ⊢
    exact Sporadic.Mathieu.M24LocalGeometry.TrioNormalSeeds.actor_le_of_seed_closure _ _
      heYP ((normal_subgroupOf_iff_le_normalizer heYP).mpr hePN) heYnot hec
  have hh : A ≤ P := by
    intro a ha
    obtain ⟨p,hp,he⟩ := hAP (mem_map_of_mem e.toMonoidHom ha)
    exact e.injective he ▸ hp
  intro a ha
  exact hh (show (⟨a,ha.1⟩ : C) ∈ A from ha)

/-- Both ambient normalizer containments in the M₂₄ point-component row,
independently of the generation-one exclusion. -/
theorem local_normalizers_le_M_of_mathieu_point_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hm : Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24)) :
    s.marking.Gi 3 ≤ s.marking.M ∧ s.marking.Gi 6 ≤ s.marking.M := by
  have step (i : ℕ) (hi : i = 3 ∨ i = 6) : s.marking.Gi i ≤ s.marking.M := by
    apply (s.local_normalizer_iff_large_point_projection h hK hLK hN (.inr (.inl hm)) i hi).mpr
    exact (s.point_projection_le_parabolic_of_mathieu h hK hLK hN hm i hi).trans
      ((s.pointCoreImage_normalizes_point_iff (s.marking.Mi 1) inf_le_right).mpr
        (s.Mi_normalizes_Li 1))
  exact ⟨step 3 (.inl rfl),step 6 (.inr rfl)⟩


/-- The Mathieu row supplies every local containment in the original source setup. -/
theorem local_containments_of_mathieu_point_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hm : Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24)) :
    s.marking.Gi 3 ≤ s.marking.M ∧ s.marking.Gi 6 ≤ s.marking.M ∧
      V ≤ (s.marking.Gi 1).pCoreIn 2 := by
  obtain ⟨h3,h6⟩ := s.local_normalizers_le_M_of_mathieu_point_component h hK hLK hN hm
  exact ⟨h3,h6,s.seed_le_point_core_from_source h⟩

/-- Source 12.5.11(2) in the Mathieu point row with both normalizer premises
discharged independently. Only the earlier structural source input remains. -/
theorem point_component_eq_of_mathieu_from_source
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    {K : Subgroup G} (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hm : Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24)) : s.marking.Li 1 = K := by
  obtain ⟨h3,h6⟩ := s.local_normalizers_le_M_of_mathieu_point_component h hK hLK hN hm
  exact s.point_component_eq_of_mathieu_of_source_parameters h structural h3 h6 hK hLK hN hm

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
