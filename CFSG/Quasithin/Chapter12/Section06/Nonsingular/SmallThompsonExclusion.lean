module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.SmallThompsonLocal
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SixLocalFF.RankTwo
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SixLocalFF.BinaryLinear
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.AlternatingSmall
public import Theory.SpecificGroups.Alternating.SevenSectionCentralizer

/-!
# Excluding the small Thompson branch on the original canonical action

Assume the original K_v is not quasisimple and escapes M. If J(T_v) lies
in Q, the checked local geometry gives a proper full-Sylow local A₆
section inside the literal simple component image. The canonical action
is FF, so its proved B.5.1 conclusion supplies actual model equivalences.
Parabolic placement and quotient orders exclude the characteristic-two
rows. Small-carrier exclusions and centerlessness leave only A₇.

The original nontrivial R_v quotient image centralizes the A₆ section.
The A₇ socle centralizer theorem makes this two-subgroup trivial, a
contradiction. This proves 12.6.14 conditional only on the remaining
nonquasisimplicity assertion 12.6.12 and the original Sylow geometry.
At the preferred point with nontrivial original C_V(L), nonquasisimplicity
is discharged, and 12.6.9 supplies both local and global Thompson generation.
No universal A.3.12 classification is assumed.

The HS/J₄ exclusions with trivial original fixed space, general 12.6.13(3),
blocks, splitting and fixed-space elimination remain open. Neither 12.6.2
nor 12.6.23 is asserted. Earlier T-invariance and TI retain producer
qt-d-1222-source, with final discharge owned by qt-d-12634-source.

Source: Aschbacher--Smith 12.6.8--15, printed pp.824--826, and B.5.1,
printed pp.99--103, combined manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

theorem SourceHypothesis.small_thompson_component_local_section
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hJ : elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L)
    (he : ¬ Kv (v : G) ≤ M L) :
    let J := Kv (v : G) ⊔ Tv T (v : G)
    let A := starImage J (Lv L (v : G))
    let B := starImage J (Kv (v : G))
    Nonempty (B ≃* Star (Kv (v : G))) ∧
      ∃ P : Sylow 2 B,
        A.subgroupOf B ∈ ChapterA.Section03.localCComponents P ∧
        A.subgroupOf B ≠ ⊤ ∧
        Nonempty (((A.subgroupOf B) ⧸ pCore 2 (A.subgroupOf B)) ≃*
          alternatingGroup (Fin 6)) := by
  let C := Kv (v : G)
  let J := C ⊔ Tv T (v : G)
  let C₀ := C.subgroupOf J
  let A := starImage J (Lv L (v : G))
  let B := starImage J C
  let q := QuotientGroup.mk' (pCore 2 J)
  have hJG : J ≤ Gv (v : G) := sup_le (Kv_le_Gv _) inf_le_right
  have hc : C₀.IsCComponent :=
    (H.nonsingular_canonical_component D v hv).1.subgroupOf_of_le le_sup_left hJG
  let c : C₀ ≃* C := subgroupOfEquivOfLe (show C ≤ J from le_sup_left)
  let e : B ≃* Star C := (cComponentTwoCoreQuotientEquiv hc).symm.trans
    (QuotientGroup.congr _ _ c (pCore_map_iso 2 c))
  let : Group.IsNilpotent (pCore 2 J) := pCore_isNilpotent
  have hb : B.IsCComponent := hc.map_quotient (pCore 2 J)
  obtain ⟨hlt,⟨ea⟩,_,_,_,_⟩ := H.small_thompson_local_embedding D v hv hs hJ he
  obtain ⟨P,_,hl⟩ := H.small_thompson_local_component D v hv hs hJ he
  obtain ⟨S,_,hS⟩ := ChapterA.Section03.SourceEmbeddings.exists_local_sylow_restriction
    P hl hlt.le hb.subnormal
  let a : A.subgroupOf B ≃* A := subgroupOfEquivOfLe hlt.le
  refine ⟨⟨e⟩,S,hS,?_,⟨(QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans ea⟩⟩
  exact fun htop => hlt.not_ge (subgroupOf_eq_top.mp htop)


private theorem SourceHypothesis.small_thompson_exclude_model
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hJ : elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L)
    (he : ¬ Kv (v : G) ≤ M L)
    {F : Type*} [Group F] [Finite F]
    (hF : ∀ (S : Sylow 2 F) (B : Subgroup F),
      B ∈ ChapterA.Section03.localCComponents S → B ≠ ⊤ →
      ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) → False)
    (e : Star (Kv (v : G)) ≃* F) : False := by
  obtain ⟨⟨c⟩,P,hl,hp,⟨a⟩⟩ := H.small_thompson_component_local_section D v hv hs hJ he
  let J := Kv (v : G) ⊔ Tv T (v : G)
  let B := starImage J (Kv (v : G))
  let A := (starImage J (Lv L (v : G))).subgroupOf B
  let f := c.trans e
  let : Group.IsSolvable f.toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr f.injective]
    infer_instance
  let d := A.equivMapOfInjective f.toMonoidHom f.injective
  apply hF (P.mapSurjective (f := f.toMonoidHom) f.surjective) (A.map f.toMonoidHom)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hl f.toMonoidHom) _
    ((QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).symm.trans a)
  intro ht
  apply hp
  apply Subgroup.map_injective (f := f.toMonoidHom) f.injective
  rw [ht,map_top_of_surjective f.toMonoidHom f.surjective]

open scoped MatrixGroups in
theorem SourceHypothesis.small_thompson_classical_exclusions
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hJ : elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L)
    (he : ¬ Kv (v : G) ≤ M L) (F : ChapterB.QuasisimpleSource.BinaryField) :
    ¬ Nonempty (Star (Kv (v : G)) ≃* SL(2,F.Carrier)) ∧
    ¬ Nonempty (Star (Kv (v : G)) ≃* SL(3,F.Carrier)) ∧
    (1 < F.degree →
      (¬ Nonempty (Star (Kv (v : G)) ≃* Matrix.symplecticGroup (Fin 2) F.Carrier)) ∧
      ¬ Nonempty (Star (Kv (v : G)) ≃* Atlas.G2.Model F.Carrier)) := by
  refine ⟨?_,?_,fun hn => ⟨?_,?_⟩⟩
  · rintro ⟨e⟩
    exact H.small_thompson_exclude_model D v hv hs hJ he
      ChapterA.Section03.SourceEmbeddings.SixLocalFF.not_linear_two e
  · rintro ⟨e⟩
    exact H.small_thompson_exclude_model D v hv hs hJ he
      (ChapterA.Section03.SourceEmbeddings.SixLocalFF.not_special_linear_three F.card_eq) e
  · rintro ⟨e⟩
    exact H.small_thompson_exclude_model D v hv hs hJ he
      (ChapterA.Section03.SourceEmbeddings.SixLocalFF.not_symplectic F.card_eq hn) e
  · rintro ⟨e⟩
    have hq : 2 < Nat.card F.Carrier := by
      rw [F.card_eq]
      exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
        (Nat.pow_le_pow_right (by decide) (by omega : 2 ≤ F.degree))
    exact H.small_thompson_exclude_model D v hv hs hJ he
      (ChapterA.Section03.SourceEmbeddings.SixLocalFF.not_g2 hq) e

theorem SourceHypothesis.small_thompson_not_binary_linear
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hJ : elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L)
    (he : ¬ Kv (v : G) ≤ M L) {d : ℕ} (hd : d = 4 ∨ d = 5) :
    ¬ ClassicalGroup.IsPSL (Star (Kv (v : G))) d 2 := by
  intro hm
  obtain ⟨⟨c⟩,P,hl,_,⟨a⟩⟩ := H.small_thompson_component_local_section D v hv hs hJ he
  exact ChapterA.Section03.SourceEmbeddings.SixLocalFF.BinaryLinear.not_section_binary_linear
    P _ hl a hd (hm.of_mulEquiv c)


theorem SourceHypothesis.small_thompson_small_exclusions
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hJ : elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L)
    (he : ¬ Kv (v : G) ≤ M L) :
    (¬ Nonempty (Star (Kv (v : G)) ≃* alternatingGroup (Fin 5))) ∧
    (¬ Nonempty (Star (Kv (v : G)) ≃* alternatingGroup (Fin 6))) ∧
    (¬ Nonempty (Star (Kv (v : G)) ≃* commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)))) ∧
    ¬ Nonempty (Star (Kv (v : G)) ≃* commutator (Atlas.G2.Model (ZMod 2))) := by
  obtain ⟨⟨c⟩,P,hl,hp,_⟩ := H.small_thompson_component_local_section D v hv hs hJ he
  let : IsQuasisimple (Star (Kv (v : G))) :=
    (H.nonsingular_canonical_component D v hv).2.2.2.1
  let : IsQuasisimple (starImage (Kv (v : G) ⊔ Tv T (v : G)) (Kv (v : G))) :=
    IsQuasisimple.of_mulEquiv c.symm
  refine ⟨?_,?_,?_,?_⟩
  · rintro ⟨e⟩
    exact ChapterA.Section03.SourceEmbeddings.FiveLocalFF.AlternatingSmall.not_proper_five
      P _ hl hp (c.trans e)
  · rintro ⟨e⟩
    exact ChapterA.Section03.SourceEmbeddings.FiveLocalFF.AlternatingSmall.not_proper_six
      P _ hl hp (c.trans e)
  · rintro ⟨e⟩
    exact ChapterA.Section03.SourceEmbeddings.FiveLocalFF.AlternatingSmall.not_proper_symplectic_two_derived
      P _ hl hp (c.trans e)
  · rintro ⟨e⟩
    exact H.small_thompson_exclude_model D v hv hs hJ he
      (fun _ B _ _ a => ChapterA.Section03.SourceEmbeddings.SixLocalFF.not_g2_two_derived
        (by simp) B a) e

open scoped MatrixGroups in
theorem SourceHypothesis.small_thompson_not_binary_special_linear
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hJ : elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L)
    (he : ¬ Kv (v : G) ≤ M L) {d : ℕ} (hd : d = 4 ∨ d = 5) :
    ¬ Nonempty (Star (Kv (v : G)) ≃* SL(d,ZMod 2)) := by
  rintro ⟨e⟩
  exact H.small_thompson_not_binary_linear D v hv hs hJ he hd
    ⟨ZMod 2,inferInstance,inferInstance,by simp,
      ⟨e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega : 0 < d)).symm⟩⟩

end CFSG.Quasithin.Chapter12.Section06



namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open ChapterB.QuasisimpleSource
open scoped MatrixGroups IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

theorem SourceHypothesis.small_thompson_component_seven
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hnot : ¬ IsQuasisimple (Kv (v : G)))
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (hJ : elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L)
    (he : ¬ Kv (v : G) ≤ M L) :
    Nonempty (Star (Kv (v : G)) ≃* alternatingGroup (Fin 7)) := by
  let J := Kv (v : G) ⊔ Tv T (v : G)
  let E := reducedTwoSubgroup J
  let : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
  let q := ChapterB.InternalThompsonAction.actionMk E
  let ρ := ChapterB.InternalThompsonAction.action E
  let B := ((Kv (v : G)).subgroupOf J).map q
  let O := offenderSubgroup ρ
  let C := B.subgroupOf O
  obtain ⟨_,_,hBO,⟨c⟩⟩ :=
    H.small_thompson_canonical_quasisimple_classification D v hv hTV hnot hs hi hJ he
  obtain ⟨_,hker,_,_,_⟩ := H.small_thompson_canonical_ff D v hv hTV hnot hs hi hJ he
  obtain ⟨b⟩ := H.nonsingular_canonical_component_image D v hv (Tv T (v : G)) inf_le_right hker
  let e : C ≃* Star (Kv (v : G)) := (subgroupOfEquivOfLe hBO).trans b
  obtain ⟨_,_,_,hq,hsi⟩ := H.nonsingular_canonical_component D v hv
  let : IsQuasisimple (Star (Kv (v : G))) := hq
  let : IsSimpleGroup (Star (Kv (v : G))) := hsi
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv e.symm
  let : IsSimpleGroup C := e.isSimpleGroup
  have hz : center C = ⊥ := by
    rcases (inferInstance : (center C).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative C (center_eq_top_iff.mp h)).elim
  have hsmall := H.small_thompson_small_exclusions D v hv hs hJ he
  have hbin := fun d hd => H.small_thompson_not_binary_special_linear D v hv hs hJ he (d := d) hd
  have height : ¬ Nonempty (Star (Kv (v : G)) ≃* alternatingGroup (Fin 8)) := by
    rintro ⟨a⟩
    exact H.small_thompson_not_binary_linear D v hv hs hJ he (d := 4) (Or.inl rfl)
      ⟨ZMod 2,inferInstance,inferInstance,by simp,
        ⟨a.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two⟩⟩
  cases c.clause_one with
  | irreducible _ _ _ hm _ =>
    cases hm with
    | linearTwo F _ a _ _ =>
      exact ((H.small_thompson_classical_exclusions D v hv hs hJ he F).1
        ⟨e.symm.trans a.groupEquiv⟩).elim
    | linearThree F _ a _ =>
      exact ((H.small_thompson_classical_exclusions D v hv hs hJ he F).2.1
        ⟨e.symm.trans a.groupEquiv⟩).elim
    | symplectic F hn _ a _ =>
      exact (((H.small_thompson_classical_exclusions D v hv hs hJ he F).2.2 hn).1
        ⟨e.symm.trans a.groupEquiv⟩).elim
    | symplecticTwo a _ => exact (hsmall.2.2.1 ⟨e.symm.trans a.subgroupEquiv⟩).elim
    | g2 F hn _ a _ _ =>
      exact (((H.small_thompson_classical_exclusions D v hv hs hJ he F).2.2 hn).2
        ⟨e.symm.trans a.groupEquiv⟩).elim
    | g2Two a _ _ => exact (hsmall.2.2.2 ⟨e.symm.trans a.subgroupEquiv⟩).elim
    | symmetric n hn a _ _ =>
      rcases hn with rfl | rfl
      · exact (hsmall.1 ⟨e.symm.trans a.subgroupEquiv⟩).elim
      · exact ⟨e.symm.trans a.subgroupEquiv⟩
    | alternatingSix _ a _ _ => exact (hsmall.2.1 ⟨e.symm.trans a.groupEquiv⟩).elim
    | alternatingSeven _ _ a _ _ _ => exact ⟨e.symm.trans a⟩
    | tripleSix _ a _ =>
      have hc := Nat.card_congr a.centerEquiv.toEquiv
      change Nat.card (center C) = Nat.card (Multiplicative (ZMod 3)) at hc
      rw [hz,card_bot] at hc
      norm_num at hc
    | binaryLinear d hd _ a _ => exact (hbin d hd ⟨e.symm.trans a.groupEquiv⟩).elim
    | orthogonalSix _ _ a _ _ => exact (height ⟨e.symm.trans a.groupEquiv⟩).elim
    | symmetricEight _ a _ => exact (height ⟨e.symm.trans a.subgroupEquiv⟩).elim
    | exteriorFive _ _ a _ _ _ => exact (hbin 5 (Or.inr rfl) ⟨e.symm.trans a⟩).elim
  | doubleThree F _ a _ _ =>
    exact ((H.small_thompson_classical_exclusions D v hv hs hJ he F).2.1
      ⟨e.symm.trans a.groupEquiv⟩).elim
  | naturalDual d hd _ hn =>
    obtain ⟨a⟩ := hn
    exact (hbin d hd ⟨e.symm.trans a.groupEquiv⟩).elim
  | repeatedNatural d _ hd _ _ _ hn =>
    obtain ⟨a⟩ := hn
    exact (hbin d hd ⟨e.symm.trans a.groupEquiv⟩).elim
end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup Theory.GroupTheory Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Source 12.6.14 under the actual nonquasisimplicity premise of 12.6.12. -/
theorem SourceHypothesis.nonsingular_thompson_not_le_core_of_not_quasisimple
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hnot : ¬ IsQuasisimple (Kv (v : G)))
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (he : ¬ Kv (v : G) ≤ M L) :
    ¬ elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L := by
  intro hJ
  let C := Kv (v : G)
  let J := C ⊔ Tv T (v : G)
  let C₀ := C.subgroupOf J
  let P₀ := (Tv T (v : G)).subgroupOf J
  let q := QuotientGroup.mk' (pCore 2 J)
  let B := starImage J C
  let A := starImage J (Lv L (v : G))
  let R := starImage J (Rv T L (v : G))
  have hJG : J ≤ Gv (v : G) := sup_le (Kv_le_Gv _) inf_le_right
  have hnC : J ≤ normalizer (C : Set G) :=
    hJG.trans ((normal_subgroupOf_iff_le_normalizer (Kv_le_Gv _)).mp (Kv_normalIn_Gv _))
  let : C₀.Normal := normal_subgroupOf_of_le_normalizer hnC
  let : B.Normal := (inferInstance : C₀.Normal).map q (QuotientGroup.mk'_surjective _)
  obtain ⟨⟨c⟩,_⟩ := H.small_thompson_component_local_section D v hv hs hJ he
  obtain ⟨e⟩ := H.small_thompson_component_seven D v hv hTV hnot hs hi hJ he
  let eB : B ≃* alternatingGroup (Fin 7) := c.trans e
  obtain ⟨_,_,_,hq,_⟩ := H.nonsingular_canonical_component D v hv
  let : IsQuasisimple (Star C) := hq
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv c.symm
  have hp : IsPGroup 2 P₀ :=
    (T.isPGroup'.to_le (show Tv T (v : G) ≤ (T : Subgroup G) from inf_le_left)).comap_subtype
  have hgen : C₀ ⊔ P₀ = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show C ≤ J from le_sup_left),
      map_subgroupOf_eq_of_le (show Tv T (v : G) ≤ J from le_sup_right),
      ←MonoidHom.range_eq_map,range_subtype]
  have hquot : IsPGroup 2 (Star J ⧸ B) :=
    isPGroup_quotient_of_sup_eq_top B (P₀.map q) (hp.map q) (by
      change C₀.map q ⊔ P₀.map q = ⊤
      rw [←Subgroup.map_sup,hgen,map_top_of_surjective q (QuotientGroup.mk'_surjective _)])
  have hF : B = generalizedFitting (Star J) :=
    (generalizedFitting_eq_of_quasisimple_two_quotient B hquot (pCore_quotient_pCore_eq_bot 2)).symm
  obtain ⟨hlt,⟨eA⟩,hRA,_,_,_⟩ := H.small_thompson_local_embedding D v hv hs hJ he
  obtain ⟨_,hR,hRp,_⟩ := H.small_thompson_local_image D v hv hs hJ he
  apply hR
  apply seven_socle_two_section_centralizer B A R hF eB hlt.le eA hRp
  apply commutator_le.mpr
  intro r hr a ha
  exact ((mem_coreQuotientCentralizer_iff A r).mp (hRA hr)).2 a ha

/-- At the original preferred escaping point with C_V(L) nontrivial,
nonquasisimplicity is already proved, so12.6.14 has no extra local premise. -/
theorem SourceHypothesis.exists_preferred_nonsingular_large_thompson_of_fixed
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hz : ZV L V ≠ ⊥)
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ w : V, D.Nonsingular w ∧ ¬ Gv (w : G) ≤ M L ∧
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
      (Tv T (w : G)).relIndex (T : Subgroup G) = 4 ∧
      Lv L (w : G) < Kv (w : G) ∧ ¬ Kv (w : G) ≤ M L ∧
      V ⊓ centralizer (Kv (w : G) : Set G) = zpowers (w : G) ∧
      ¬ IsQuasisimple (Kv (w : G)) ∧ IsSimpleGroup (Star (Kv (w : G))) ∧
      ¬ elementaryAbelianMaxJ (Tv T (w : G)) ≤ Q T L ∧
      ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ Q T L ∧
      Lv L (w : G) = ⁅Lv L (w : G),elementaryAbelianMaxJ (Tv T (w : G))⁆ ∧
      L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
  obtain ⟨w,hw,he,hs,hi,hlt,hnot,_,_,hsimple,hline,hfixed,_⟩ :=
    SourceHypothesis.exists_preferred_nonsingular_nontrivial_fixed_not_quasisimple.{_,0}
      H D hTV hTI v hv he
  have hJ := H.nonsingular_thompson_not_le_core_of_not_quasisimple
    D w hw hTV (hfixed hz) hs hi hnot
  exact ⟨w,hw,he,hs,hi,hlt,hnot,hline,hfixed hz,hsimple,hJ,
    H.nonsingular_thompson_generation D w hw hTV hs hJ⟩
end CFSG.Quasithin.Chapter12.Section06
