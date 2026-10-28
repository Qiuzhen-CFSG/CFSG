module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.MixedKernel
public import Theory.SpecificGroups.BinaryLinear.FivePointSection.AdjacentKernel

/-!
# Plane movement in every surviving point-component model

The original mixed section has one of three GL₅(2) flag types. The literal
normal sixteen-group kernel is an endpoint radical in each type, whose
normalizer cannot normalize the original two-residual. Thus the mixed section
is impossible. Together with the existing alternating-seven and matching
binary calculations, this proves movement, all three clauses of source 12.9.6,
and the actual LocalControl application with no movement premise.

The point-quotient centralizer bound, the surviving model list and the plane
centralizer bound still require source proofs by qt-d-1291-natural-source;
the component and abelian-span obligations also remain with that owner.
The proofs preserve the original chosen module, literal point quotient and
conjugation action. Source: Aschbacher--Smith, 12.9.6, printed pp.861--862.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag Section08.NormalGeometry
open BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

omit [Finite G] in
/-- Neither adjacent flag supports the actual kernel-normalizer restriction. -/
theorem no_mixedAdjacentPointSection [IsElementaryAbelian 2 V]
    (F : InvariantFlag T V n) (C : ComponentGeometry F L) :
    ¬ MixedAdjacentPointSection F C := by
  rintro ⟨e,a,_,_,_,hp,hres,hn,hJ,hk,b,hflag⟩
  let X := C.K1 ⊔ (T : Subgroup G)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  let r := q.comp (inclusion (sup_le_sup_right C.contains (T : Subgroup G)))
  let J := r.range
  let Q := a.ker.map J.subtype
  have hQJ : Q ≤ J := map_subtype_le _
  have hJN : J ≤ normalizer (Q : Set (LinearGroup 5)) := by
    apply (normal_subgroupOf_iff_le_normalizer hQJ).mp
    change ((a.ker.map J.subtype).comap J.subtype).Normal
    rw [comap_map_eq_self_of_injective J.subtype_injective]
    infer_instance
  have hc : Nat.card Q = 16 := (card_map_of_injective J.subtype_injective).trans hk
  rcases hflag with he | he
  · have hh := BinaryLinear.FivePointSection.AdjacentKernel.no_first_kernel b Q
      (hp.map _) hc (by rwa [←he]) (by rwa [←he]) (by rwa [←he])
    apply hh
    rw [←he,←hres]
    exact hn
  · have hh := BinaryLinear.FivePointSection.AdjacentKernel.no_last_kernel b Q
      (hp.map _) hc (by rwa [←he]) (by rwa [←he]) (by rwa [←he])
    apply hh
    rw [←he,←hres]
    exact hn

omit [Finite G] in
/-- All three flags are incompatible with the literal source kernel and residual. -/
theorem no_mixedPointSection [IsElementaryAbelian 2 V]
    (F : InvariantFlag T V n) (C : ComponentGeometry F L) : ¬ MixedPointSection F C :=
  fun hs => no_mixedAdjacentPointSection F C (mixedPointSection_adjacent F C hs)

/-- The mixed n=4/PSL₅(2) point component moves the original plane. -/
theorem point_core_moves_plane_of_mixed_binary
    (h : HigherRankHypothesis K T L V 4) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V 4) (C : ComponentGeometry F L)
    (hm : ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 5 2) :
    ⁅F.Vi 2,C.K1.pCoreIn 2⁆ ≠ ⊥ := by
  let := h.chosen.elementary
  intro hfix
  exact no_mixedPointSection F C (mixed_plane_fixed_section h earlier F C hm hfix)

/-- The complete movement assertion of 12.9.6(1) under source 12.9.5(1--2).
No transvection-marking or kernel-comparison premise remains. -/
theorem point_core_moves_plane_of_controlled_models
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n) (C : ComponentGeometry F L)
    (hcentral : pointQuotientCentralizer C ≤ normalizer (L : Set G))
    (hmodels : Chapter1.Section02.LocalModels.IsAlternating (C.K1 ⧸ pCore 2 C.K1) 7 ∨
      ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 4 2 ∨
      ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 5 2) :
    ⁅F.Vi 2,C.K1.pCoreIn 2⁆ ≠ ⊥ := by
  intro hfix
  obtain ⟨rfl,hm⟩ := point_movement_failure_is_mixed h hn earlier F C hcentral hmodels hfix
  exact point_core_moves_plane_of_mixed_binary h earlier F C hm hfix

/-- All three source 12.9.6 clauses on the original plane normal closure,
including relative normality, its exact core, quotient and minimal-parabolic property. -/
theorem plane_local_control_of_controlled_models
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n) (C : ComponentGeometry F L)
    (hcentral : pointQuotientCentralizer C ≤ normalizer (L : Set G))
    (hmodels : Chapter1.Section02.LocalModels.IsAlternating (C.K1 ⧸ pCore 2 C.K1) 7 ∨
      ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 4 2 ∨
      ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 5 2) :
    ⁅F.Vi 2, C.K1.pCoreIn 2⁆ ≠ ⊥ ∧
      ((planeCoreClosure F).subgroupOf (F.Gi 2)).Normal ∧
      planeCoreClosure F ⊔ (T : Subgroup G) = F.P L ∧
      ChapterB.IsMinimalParabolicOver T (planeCoreClosure F ⊔ (T : Subgroup G)) ∧
      (T : Subgroup G).relIndex (planeCoreClosure F ⊔ (T : Subgroup G)) = 3 ∧
      (planeCoreClosure F).pCoreIn 2 = planeCoreClosure F ⊓ centralizer (F.Vi 2 : Set G) ∧
      Nonempty (((planeCoreClosure F) ⧸ pCore 2 (planeCoreClosure F)) ≃* Equiv.Perm (Fin 3)) ∧
      primeRank 3 (centralizer (F.Vi 2 : Set G)) ≤ 1 := by
  have hmove := point_core_moves_plane_of_controlled_models h hn earlier F C hcentral hmodels
  exact ⟨hmove,plane_local_control_with_minimal_parabolic h earlier F C hmove⟩

/-- Actual LocalControl assembly after discharging movement in every surviving
model. Both centralizer bounds and the surviving-model list retain their source owner. -/
theorem localControl_of_centralizers_and_models
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n) (C : ComponentGeometry F L)
    (hcentral : pointQuotientCentralizer C ≤ normalizer (L : Set G))
    (hmodels : Chapter1.Section02.LocalModels.IsAlternating (C.K1 ⧸ pCore 2 C.K1) 7 ∨
      ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 4 2 ∨
      ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 5 2)
    (hplane : centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G)) : LocalControl C :=
  localControl_of_plane_centralizer_and_models h earlier F C hcentral hmodels
    (point_core_moves_plane_of_controlled_models h hn earlier F C hcentral hmodels) hplane
end CFSG.Quasithin.Chapter12.Section09.NaturalSource
