module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.GeneralCanonical
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.CanonicalSevenModule
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalCoreBound

/-!
# Fixed-free canonical modules at the original nonsingular point

The natural A7 moved module has zero component fixed space. If it contained
the original V_v, the original local fixed line would therefore be moved by
K_v. The unchanged projection V -> V/C_V(L) then forces C_V(L) nontrivial.
This proves the A7 branch of 12.6.18(3) before any splitting argument.

In the fixed-free branch, the actual FF catalogue consequently contains
only SL4(2) and SL5(2). Both are excluded when |S:T_v| <= 2, so the source
index bound forces |S:T_v|=4 and the same S is ambient Sylow. The final
consumer constructs the general 12.6.13 geometry and applies this sieve to
an escaping nonquasisimple residual, using the proved fixed-free reduction.
The FF premise is explicit in this branch; it is already discharged in
the separate nontrivial-fixed-space branch. Its fixed-free discharge,
these two remaining canonical rows, HS/J4, fusion and 12.6.23 remain with
this owner. Earlier invariance/TI retain qt-d-1222-source and final source
discharge retains qt-d-12634-source. Neither 12.6.2 nor 12.6.23 is asserted.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
12.6.13 and 12.6.18, printed pp.826--827, and B.5.1.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original local fixed line cannot be central in a natural A7 moved module. -/
theorem SourceHypothesis.fixed_ne_bot_of_canonical_seven
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (S : Sylow 2 (Gv (v : G)))
    (hred : U (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) =
      (reducedTwoSubgroup (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G)).map
        (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G).subtype)
    (hm : Vv L V (v : G) ≤ ⁅U (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype),Kv (v : G)⁆)
    (hseven : let J := Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
      let E := reducedTwoSubgroup J
      letI : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
      CanonicalSevenMoved E ((Kv (v : G)).subgroupOf J)) : ZV L V ≠ ⊥ := by
  let J := Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let E := reducedTwoSubgroup J
  let : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
  have hc := (canonical_seven_moved_properties_map E ((Kv (v : G)).subgroupOf J)
    hseven J.subtype J.subtype_injective).2.1
  rw [map_commutator,map_subgroupOf_eq_of_le (show Kv (v : G) ≤ J from le_sup_left),←hred] at hc
  apply D.fixed_ne_bot_of_local_line_moved H.chosen v hv
  intro hline
  have hz : ZV (Lv L (v : G)) (Vv L V (v : G)) = ⊥ :=
    bot_unique ((le_inf (inf_le_left.trans hm) hline).trans hc.le)
  have hh := D.nonsingular_moved_fixed_card H.chosen v hv
  rw [hz,card_bot] at hh
  norm_num at hh

/-- In the fixed-free branch the canonical FF catalogue contains only the two
binary linear groups, and its selected Sylow is ambient of index four over T_v. -/
theorem SourceHypothesis.fixed_free_canonical_ff_models
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (he : ¬ Kv (v : G) ≤ M L) (hz : ZV L V = ⊥)
    (S : Sylow 2 (Gv (v : G)))
    (hTS : Tv T (v : G) ≤ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype)
    (hRN : R L (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) (v : G) ≤
      normalizer (Lv L (v : G) : Set G))
    (hred : U (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) =
      (reducedTwoSubgroup (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G)).map
        (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G).subtype)
    (hm : Vv L V (v : G) ≤ ⁅U (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype),Kv (v : G)⁆)
    (hker : centralizer (reducedTwoSubgroup (Kv (v : G) ⊔
      (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G) :
      Set (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G)) =
        pCore 2 (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G))
    (hff : let E := reducedTwoSubgroup (Kv (v : G) ⊔
      (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G)
      letI : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
      IsFFModule (ChapterB.InternalThompsonAction.action E)) :
    (Nonempty (Star (Kv (v : G)) ≃* SL(4,ZMod 2)) ∨
      Nonempty (Star (Kv (v : G)) ≃* SL(5,ZMod 2))) ∧
      (Tv T (v : G)).relIndex ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) = 4 ∧
      ∃ P : Sylow 2 G, (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype = (P : Subgroup G) := by
  have hnseven : ¬ Nonempty (Star (Kv (v : G)) ≃* alternatingGroup (Fin 7)) := by
    intro hs
    exact H.fixed_ne_bot_of_canonical_seven D v hv S hred hm
      (H.nonsingular_canonical_seven_moved D v hv S hs hred hm hker hff) hz
  have hmodels := (H.nonsingular_canonical_ff_models D v hv hTV hi he S hRN hker hff).resolve_left hnseven
  let P₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let A := Tv T (v : G)
  have htwo : ¬ A.relIndex P₀ ≤ 2 := fun h => hnseven
    (H.nonsingular_canonical_ff_seven_of_index_two D v hv hTV hi he S h hRN hker hff)
  have hbound : A.relIndex P₀ ≤ 4 := by
    simpa only [hi] using Tv_relIndex_le T (v : G) P₀ (S.isPGroup'.map _) hTS
  have hthree : A.relIndex P₀ ≠ 3 := by
    intro h
    obtain ⟨n,hn⟩ := (S.isPGroup'.map (Gv (v : G)).subtype).exists_card_eq
    have hd : 3 ∣ 2 ^ n := hn ▸ (h ▸ A.relIndex_dvd_card P₀)
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  have hidx : A.relIndex P₀ = 4 := by omega
  refine ⟨hmodels,hidx,?_⟩
  have h1 := (A.subgroupOf P₀).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hTS).toEquiv] at h1
  change Nat.card A * A.relIndex P₀ = Nat.card P₀ at h1
  have h2 := (A.subgroupOf (T : Subgroup G)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (show A ≤ (T : Subgroup G) from inf_le_left)).toEquiv] at h2
  change Nat.card A * A.relIndex (T : Subgroup G) = Nat.card T at h2
  have hecard : Nat.card P₀ = Nat.card T := by
    rw [←h1,hidx,←h2]
    exact congrArg (Nat.card A * ·) hi.symm
  obtain ⟨P,hP⟩ := (S.isPGroup'.map (Gv (v : G)).subtype).exists_le_sylow
  exact ⟨P,eq_of_le_of_card_ge hP (by rw [hecard,Nat.card_congr (P.equiv T).toEquiv])⟩

/-- The actual escaping nonquasisimple source branch supplies all canonical
geometry. Only FF remains before the binary linear and ambient-Sylow reduction. -/
theorem SourceHypothesis.nonsingular_escaping_canonical_linear_reduction
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (hnot : ¬ IsQuasisimple (Kv (v : G)))
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (he : ¬ Kv (v : G) ≤ M L) :
    ZV L V = ⊥ ∧ IsSimpleGroup (Star (Kv (v : G))) ∧
    ∃ S : Sylow 2 (Gv (v : G)),
      let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
      let J := Kv (v : G) ⊔ S₀
      let E := reducedTwoSubgroup J
      letI : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
      Tv T (v : G) ≤ S₀ ∧
      R L (Kv (v : G)) S₀ (v : G) = S₀ ⊓ coreQuotientCentralizer (Lv L (v : G)) ∧
      generalizedFitting J = pCore 2 J ∧ centralizer (E : Set J) = pCore 2 J ∧
      U (Kv (v : G)) S₀ = E.map J.subtype ∧
      Vv L V (v : G) ≤ ⁅U (Kv (v : G)) S₀,Kv (v : G)⁆ ∧
      (IsFFModule (ChapterB.InternalThompsonAction.action E) →
        (Nonempty (Star (Kv (v : G)) ≃* SL(4,ZMod 2)) ∨
          Nonempty (Star (Kv (v : G)) ≃* SL(5,ZMod 2))) ∧
        (Tv T (v : G)).relIndex S₀ = 4 ∧
        ∃ P : Sylow 2 G, S₀ = (P : Subgroup G)) := by
  have hz := H.fixed_eq_bot_of_nonsingular_escape D hTV hTI v hv
    (fun h => he ((Kv_le_Gv (v : G)).trans h))
  obtain ⟨hsimple,S,hTS,_,hReq,hFit,hker,hred,hm⟩ :=
    H.nonsingular_nonquasisimple_canonical_structure D v hv hTV hnot hs hi
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let J := Kv (v : G) ⊔ S₀
  let E := reducedTwoSubgroup J
  let : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
  have hk : centralizer (E : Set J) = pCore 2 J := by
    rw [hred] at hker
    change centralizer ((E.map J.subtype).comap J.subtype : Set J) = _ at hker
    rwa [comap_map_eq_self_of_injective J.subtype_injective] at hker
  exact ⟨hz,hsimple,S,hTS,hReq,hFit,hk,hred,hm,
    H.fixed_free_canonical_ff_models D v hv hTV hi he hz S hTS
      (hReq.le.trans (inf_le_right.trans (coreQuotientCentralizer_le_normalizer _)))
      hred hm hk⟩

end CFSG.Quasithin.Chapter12.Section06
