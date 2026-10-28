module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.PreferredCanonical
public import Theory.SpecificGroups.BinaryLinear.SixSectionSmallIndex

/-!
# Canonical component exclusions from the selected relative Sylow index

Intersect the same selected Sylow of G_v with the relatively normal K_v,
then map through the literal two-core quotient. The original T_v normalizes
L_v and V_v, so its actual index bound survives in every model. When that
bound is two, the native A8 and GL5(2) A6-section normalizer bounds exclude
SL4(2) and SL5(2), without assuming a whole model Sylow normalizes the section.

The canonical FF classifier therefore leaves only A7. The FF witness is
still explicit; PreferredCanonicalSeven applies the exclusions at the
unchanged preferred point and discharges the index premise.
Source: Aschbacher--Smith 12.6.18, printed p.827, combined manuscript
of 1 March 2004. Neither 12.6.2 nor 12.6.23 is asserted here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The literal local images retain the bound from the supplied selected Sylow. -/
theorem SourceHypothesis.nonsingular_local_model_sylow_index_of_selected
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (S : Sylow 2 (Gv (v : G)))
    (n : ℕ)
    (hSi : (Tv T (v : G)).relIndex
      ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) ≤ n)
    {F : Type*} [Group F] [Finite F]
    (f : Kv (v : G) →* F) (hf : Function.Surjective f) :
    let B := ((Lv L (v : G)).subgroupOf (Kv (v : G))).map f
    let W := ((Vv L V (v : G)).subgroupOf (Kv (v : G))).map f
    ∃ P : Sylow 2 F,
      (normalizer (B : Set F) ⊓ normalizer (W : Set F)).relIndex
        (P : Subgroup F) ≤ n := by
  let C := Kv (v : G)
  let B := (Lv L (v : G)).subgroupOf C
  let W := (Vv L V (v : G)).subgroupOf C
  let N := normalizer (B.map f : Set F) ⊓ normalizer (W.map f : Set F)
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  have hSyl : Chapter1.IsSylowIn 2 S₀ (Gv (v : G)) := ⟨S,rfl⟩
  obtain ⟨P,hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hSyl
    (Kv_le_Gv (v : G)) (Kv_normalIn_Gv (v : G)).isSubnormal
  have hBC : Lv L (v : G) ≤ C := Lv_le_Kv_of_A6 L (v : G)
    (Classical.choice (D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv))
  have hWC : Vv L V (v : G) ≤ C := (H.nonsingular_component_rank D v hv).1
  have hnB : Tv T (v : G) ≤ normalizer (Lv L (v : G) : Set G) :=
    (inf_le_inf H.chosen.sylow_normalizes_component le_rfl).trans
      (Mv_le_normalizer_Lv L (v : G))
  have hnW : Tv T (v : G) ≤ normalizer (Vv L V (v : G) : Set G) :=
    normalizes_Vv_of_normalizes _ _ (inf_le_left.trans hTV) hnB
  have hnBC : (Tv T (v : G)).subgroupOf C ≤ normalizer (B : Set C) := by
    rw [←subgroupOf_normalizer_eq hBC]
    exact comap_mono hnB
  have hnWC : (Tv T (v : G)).subgroupOf C ≤ normalizer (W : Set C) := by
    rw [←subgroupOf_normalizer_eq hWC]
    exact comap_mono hnW
  have hn : (Tv T (v : G)).subgroupOf C ≤ N.comap f := by
    apply map_le_iff_le_comap.mp
    exact le_inf ((map_mono hnBC).trans (le_normalizer_map f))
      ((map_mono hnWC).trans (le_normalizer_map f))
  refine ⟨P.mapSurjective hf,?_⟩
  change N.relIndex ((P : Subgroup C).map f) ≤ n
  rw [←relIndex_comap]
  apply (relIndex_le_of_le_left hn index_ne_zero_of_finite).trans
  change ((Tv T (v : G)).comap C.subtype).relIndex (P : Subgroup C) ≤ n
  rw [relIndex_comap,hP]
  exact (relIndex_le_of_le_right inf_le_left index_ne_zero_of_finite).trans hSi

private theorem SourceHypothesis.nonsingular_exclude_index_two_model
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (S : Sylow 2 (Gv (v : G)))
    (hi : (Tv T (v : G)).relIndex
      ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) ≤ 2)
    {F : Type*} [Group F] [Finite F]
    (hF : ∀ (A : Subgroup F) [Group.IsPerfect A],
      ((A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 6)) →
      ∀ S : Sylow 2 F, (normalizer (A : Set F)).relIndex S ≤ 2 → False)
    (e : Star (Kv (v : G)) ≃* F) : False := by
  let C := Kv (v : G)
  let A₀ := (Lv L (v : G)).subgroupOf C
  let q := QuotientGroup.mk' (pCore 2 C)
  let f := e.toMonoidHom.comp q
  let A := A₀.map f
  have hAC : Lv L (v : G) ≤ C := (H.nonsingular_canonical_component D v hv).2.1
  let a : A₀ ≃* Lv L (v : G) := subgroupOfEquivOfLe hAC
  obtain ⟨eA⟩ := D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv
  let : Group.IsPerfect (Lv L (v : G)) := Lv_isPerfect_of_A6 L (v : G) eA
  let : Group.IsPerfect A₀ := Group.IsPerfect.ofSurjective
    (f := a.symm.toMonoidHom) a.symm.surjective
  let : Group.IsPerfect A := Group.IsPerfect.map f
  have hk : f.ker ≤ pCore 2 C := by
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    exact e.injective (hx.trans e.map_one.symm)
  have hkA : IsPGroup 2 (f.subgroupMap A₀).ker := by
    rw [Subgroup.ker_subgroupMap]
    exact (pCore_isPGroup.to_le hk).comap_subtype
  let b : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 6) :=
    ((f.subgroupMap A₀).pCoreQuotientEquiv (f.subgroupMap_surjective A₀) hkA).symm.trans
      ((QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans eA)
  obtain ⟨S,hS⟩ := H.nonsingular_local_model_sylow_index_of_selected D v hv hTV S 2 hi f
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  exact hF A b S ((relIndex_le_of_le_left inf_le_left index_ne_zero_of_finite).trans hS)

/-- The original index-two bound excludes both higher binary linear models,
without any FF premise or full-Sylow normalization of the A6 image. -/
theorem SourceHypothesis.nonsingular_canonical_binary_exclusions_of_index_two
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (S : Sylow 2 (Gv (v : G)))
    (hi : (Tv T (v : G)).relIndex
      ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) ≤ 2) :
    ¬ Nonempty (Star (Kv (v : G)) ≃* SL(4,ZMod 2)) ∧
      ¬ Nonempty (Star (Kv (v : G)) ≃* SL(5,ZMod 2)) := by
  constructor
  · rintro ⟨e⟩
    apply H.nonsingular_exclude_index_two_model D v hv hTV S hi
      (F := alternatingGroup (Fin 8)) _
      (e.trans ((BinaryLinear.OuterCyclic.projectiveEquivSL (by decide : 0 < 4)).symm.trans
        Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm))
    intro A _ a P hP
    have hb := Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings.six_section_sylow_index_ge_four A a P
    omega
  · rintro ⟨e⟩
    let : Finite (BinaryLinear.OuterCyclic.LinearGroup 5) :=
      Finite.of_injective (fun g : BinaryLinear.OuterCyclic.LinearGroup 5 =>
        (g : BinaryLinear.OuterCyclic.Space 5 → BinaryLinear.OuterCyclic.Space 5))
        DFunLike.coe_injective
    exact H.nonsingular_exclude_index_two_model D v hv hTV S hi
      (fun A _ a P hP => BinaryLinear.QuinticNormalizer.six_section_not_small_index A a P hP)
      (e.trans (BinaryLinear.OuterCyclic.slEquivLinear 5))

/-- The actual canonical FF component is A7 when the selected source Sylow
has index at most two over T_v. -/
theorem SourceHypothesis.nonsingular_canonical_ff_seven_of_index_two
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (he : ¬ Kv (v : G) ≤ M L)
    (S : Sylow 2 (Gv (v : G)))
    (hidx : (Tv T (v : G)).relIndex
      ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) ≤ 2)
    (hRN : R L (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) (v : G) ≤
      normalizer (Lv L (v : G) : Set G))
    (hker : centralizer (reducedTwoSubgroup (Kv (v : G) ⊔
      (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G) :
      Set (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G)) =
        pCore 2 (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G))
    (hff : let E := reducedTwoSubgroup (Kv (v : G) ⊔
      (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G)
      letI : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
      Representation.BinaryOffender.IsFFModule (ChapterB.InternalThompsonAction.action E)) :
    Nonempty (Star (Kv (v : G)) ≃* alternatingGroup (Fin 7)) := by
  have hn := H.nonsingular_canonical_binary_exclusions_of_index_two D v hv hTV S hidx
  exact (H.nonsingular_canonical_ff_models D v hv hTV hi he S hRN hker hff).resolve_right
    (fun h => h.elim hn.1 hn.2)

end CFSG.Quasithin.Chapter12.Section06
