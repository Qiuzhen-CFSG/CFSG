module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.OrderObstruction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.Transport
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.Recognition.Geometry

/-!
# Algebraic reduction of rank-two quotient parabolic recognition

The local component intersection is proper: a normal quasisimple subgroup
cannot lie in a group whose generalized Fitting subgroup is a two-group.
The quotient Sylow subgroup normalizes both that intersection and its
intrinsic Sylow normalizer. Their join is therefore invariant.

If this join is proper and the proper invariant Borel overgroups have
self-centralizing two-cores, characteristic two passes to their Sylow
extensions. The characteristic-two maximality from 15.3.41 then identifies
the join with the local intersection and proves the exact maximality clause.
Both geometric assertions remain explicit in the final theorem below.

The generic extension argument is reused from the rank-one development;
none of its rank-one configuration or shadow hypotheses is imported into
the proof. All component images use the actual quotient by the centralizer.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.41,
printed p.1138, and the first paragraph of the final proof of 15.3.35,
printed p.1139. The remaining geometry must retain every action alternative
in 1.1.5(3)(a)--(c), printed pp.501--502.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection

namespace Recognition

variable {H : Type*} [Group H]

/-- The intrinsic normalizer agrees with the ambient-intersection convention. -/
theorem sylowBorel_eq_borel (D T : Subgroup H) :
    sylowBorel D T = ChapterF.Source.borel D T := by
  rw [sylowBorel, ← inf_subgroupOf_right T D,
    ← subgroupOf_normalizer_eq (show T ⊓ D ≤ D from inf_le_right),
    subgroupOf_map_subtype]
  exact inf_comm _ _

/-- A subgroup normalizes the Borel of its intersection with a normal component. -/
theorem sylow_normalizes_borel (D T : Subgroup H) [D.Normal] :
    T ≤ normalizer (sylowBorel D T : Set H) := by
  rw [sylowBorel_eq_borel, ChapterF.Source.borel]
  have hD : T ≤ normalizer (D : Set H) := by
    rw [normalizer_eq_top]
    exact le_top
  exact (le_inf hD
    (((le_inf T.le_normalizer hD).trans inf_normalizer_le_normalizer_inf).trans
      (normalizer _).le_normalizer)).trans inf_normalizer_le_normalizer_inf

private theorem intersection_proper [Finite H] (D N : Subgroup H)
    [D.Normal] [IsQuasisimple D]
    (hN : generalizedFitting N = pCore 2 N) : N ⊓ D < D := by
  refine lt_of_le_of_ne inf_le_right ?_
  intro he
  have hDN : D ≤ N := he ▸ inf_le_left
  let E := D.subgroupOf N
  let : E.Normal := inferInstance
  let : IsQuasisimple E := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hDN).symm
  have hE : IsComponent N E := ⟨(inferInstance : E.Normal).isSubnormal, inferInstance⟩
  have hEp : E ≤ pCore 2 N := hN ▸ component_le_generalizedFitting N E hE
  let : Group.IsNilpotent E := (pCore_isPGroup.to_le hEp).isNilpotent
  let : IsSimpleGroup (E ⧸ center E) := IsQuasisimple.simple
  let : Nontrivial E := (QuotientGroup.mk'_surjective (center E)).nontrivial
  exact Group.IsPerfect.not_isSolvable E inferInstance

end Recognition

variable {G : Type*} [Group G] [Finite G]
variable {L MI Yplus S : Subgroup G} [L.Normal]

omit [Finite G] in
/-- The actual component and Sylow images generate the centralizer quotient. -/
theorem Setup.quotient_generated (d : Setup L MI Yplus S) :
    centralizerQuotientComponent L ⊔ S.map (centralizerQuotientMap L) = ⊤ := by
  change L.map (centralizerQuotientMap L) ⊔ S.map (centralizerQuotientMap L) = ⊤
  rw [← Subgroup.map_sup, d.generated]
  exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

/-- Characteristic two excludes containment of the nontrivial perfect component. -/
theorem Setup.quotient_intersection_proper (d : Setup L MI Yplus S) :
    MI.map (centralizerQuotientMap L) ⊓ centralizerQuotientComponent L <
      centralizerQuotientComponent L := by
  let := d.quasisimple
  let q := centralizerQuotientMap L
  let D := centralizerQuotientComponent L
  let : D.Normal := (inferInstance : L.Normal).map q (QuotientGroup.mk'_surjective _)
  let : IsSimpleGroup D := centralizerQuotientComponent_simple L
  let : IsQuasisimple D := IsQuasisimple.of_surjective (q.subgroupMap L)
    (q.subgroupMap_surjective L)
  exact Recognition.intersection_proper D _ d.quotient_local.characteristicTwo

omit [Finite G] in
/-- The quotient Sylow subgroup normalizes the local component intersection. -/
theorem Setup.quotient_intersection_invariant (d : Setup L MI Yplus S) :
    S.map (centralizerQuotientMap L) ≤ normalizer
      (MI.map (centralizerQuotientMap L) ⊓ centralizerQuotientComponent L :
        Set (CentralizerQuotient L)) := by
  let q := centralizerQuotientMap L
  let D := centralizerQuotientComponent L
  let : D.Normal := (inferInstance : L.Normal).map q (QuotientGroup.mk'_surjective _)
  apply (le_inf (d.quotient_local.sylow_le.trans (MI.map q).le_normalizer)
    (show S.map q ≤ normalizer (D : Set (CentralizerQuotient L)) from ?_)).trans
      inf_normalizer_le_normalizer_inf
  rw [normalizer_eq_top]
  exact le_top

omit [Finite G] in
/-- Invariance of the proposed hull requires no model inspection. -/
theorem Setup.quotient_borel_join_invariant (d : Setup L MI Yplus S) :
    S.map (centralizerQuotientMap L) ≤ normalizer
      ((sylowBorel (centralizerQuotientComponent L) (S.map (centralizerQuotientMap L)) ⊔
        (MI.map (centralizerQuotientMap L) ⊓ centralizerQuotientComponent L) :
          Subgroup (CentralizerQuotient L)) : Set (CentralizerQuotient L)) := by
  let q := centralizerQuotientMap L
  let D := centralizerQuotientComponent L
  let : D.Normal := (inferInstance : L.Normal).map q (QuotientGroup.mk'_surjective _)
  exact (le_inf (Recognition.sylow_normalizes_borel D (S.map q))
    d.quotient_intersection_invariant).trans
      ((sylowBorel D (S.map q)).normalizer_inf_normalizer_le_normalizer_sup (MI.map q ⊓ D))

/-- Restrict the actual quotient Sylow subgroup to its normal component. -/
theorem Setup.quotient_component_sylow (d : Setup L MI Yplus S) :
    ∃ P : Sylow 2 (centralizerQuotientComponent L),
      (P : Subgroup (centralizerQuotientComponent L)).map
        (centralizerQuotientComponent L).subtype =
          S.map (centralizerQuotientMap L) ⊓ centralizerQuotientComponent L := by
  let q := centralizerQuotientMap L
  let D := centralizerQuotientComponent L
  let : D.Normal := (inferInstance : L.Normal).map q (QuotientGroup.mk'_surjective _)
  obtain ⟨T, hT⟩ := d.quotient_local.sylow
  obtain ⟨P, hP⟩ := T.exists_subgroupOf_eq_of_normal D
  refine ⟨P, ?_⟩
  rw [hP, hT, subgroupOf_map_subtype]

omit [Finite G] in
/-- Reduce hull properness to the component itself, with its specified Sylow. -/
theorem quotient_borel_join_proper_iff
    (P : Sylow 2 (centralizerQuotientComponent L))
    (hP : (P : Subgroup (centralizerQuotientComponent L)).map
      (centralizerQuotientComponent L).subtype =
        S.map (centralizerQuotientMap L) ⊓ centralizerQuotientComponent L) :
    (sylowBorel (centralizerQuotientComponent L) (S.map (centralizerQuotientMap L)) ⊔
      (MI.map (centralizerQuotientMap L) ⊓ centralizerQuotientComponent L) <
        centralizerQuotientComponent L) ↔
    (normalizer (P : Set (centralizerQuotientComponent L)) ⊔
      (MI.map (centralizerQuotientMap L)).subgroupOf (centralizerQuotientComponent L) < ⊤) := by
  let D := centralizerQuotientComponent L
  have he : (P : Subgroup D) = (S.map (centralizerQuotientMap L)).subgroupOf D := by
    apply map_injective D.subtype_injective
    rw [hP, subgroupOf_map_subtype]
  have hn : normalizer (P : Set D) =
      normalizer ((S.map (centralizerQuotientMap L)).subgroupOf D : Set D) := by
    change normalizer ((P : Subgroup D) : Set D) = _
    rw [he]
  rw [← map_lt_map_iff_of_injective D.subtype_injective, Subgroup.map_sup,
    hn, subgroupOf_map_subtype, ← MonoidHom.range_eq_map, range_subtype]
  rfl

/-- Conditional recognition with precisely two geometric obligations.
The source-theorem owner must prove both before claiming recognition. -/
theorem quotientParabolic_of_borel_join_and_cores (d : Setup L MI Yplus S)
    (hjoin : sylowBorel (centralizerQuotientComponent L)
        (S.map (centralizerQuotientMap L)) ⊔
          (MI.map (centralizerQuotientMap L) ⊓ centralizerQuotientComponent L) <
            centralizerQuotientComponent L)
    (hcores : ∀ Q : Subgroup (CentralizerQuotient L),
      sylowBorel (centralizerQuotientComponent L) (S.map (centralizerQuotientMap L)) ≤ Q →
      Q < centralizerQuotientComponent L →
      S.map (centralizerQuotientMap L) ≤ normalizer (Q : Set (CentralizerQuotient L)) →
      centralizer (pCore 2 Q : Set Q) ≤ pCore 2 Q) :
    QuotientParabolic L MI S := by
  let q := centralizerQuotientMap L
  let D := centralizerQuotientComponent L
  let T := S.map q
  let N := MI.map q
  let : D.Normal := (inferInstance : L.Normal).map q (QuotientGroup.mk'_surjective _)
  obtain ⟨P, hP⟩ := d.quotient_local.sylow
  have hmax : Maximal (fun X : Subgroup (CentralizerQuotient L) =>
      generalizedFitting X = pCore 2 X) N :=
    ⟨d.quotient_local.characteristicTwo,
      fun J hJ hNJ => (d.quotient_local.maximal J hNJ hJ).le⟩
  have hhull : RankOne.EvenModels.ParabolicInspection.InvariantHull D T N := by
    refine ⟨sylowBorel D T ⊔ (N ⊓ D), ?_, hjoin,
      d.quotient_borel_join_invariant, le_sup_right⟩
    rw [← Recognition.sylowBorel_eq_borel]
    exact le_sup_left
  have hc : RankOne.EvenModels.ParabolicInspection.ParabolicCores D T := by
    intro Q hBQ hQD hnQ
    exact hcores Q ((Recognition.sylowBorel_eq_borel D T).symm ▸ hBQ) hQD hnQ
  have h := RankOne.EvenModels.ParabolicInspection.maximalInvariantParabolic_of_geometry
    D T N d.quotient_generated (show IsPGroup 2 (S.map q) from hP ▸ P.isPGroup') d.quotient_local.sylow_le hmax hhull hc
  refine ⟨?_, h.proper, h.invariant, ?_⟩
  · rw [Recognition.sylowBorel_eq_borel]
    exact h.contains_borel
  · intro Q hBQ hQD hnQ hPQ
    apply h.maximal Q _ hQD hnQ hPQ
    rwa [← Recognition.sylowBorel_eq_borel]

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection
