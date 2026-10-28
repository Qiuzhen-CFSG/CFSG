module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.NormalizerLocal
public import Theory.SpecificGroups.PSL3.BinaryCenterRank
public import Theory.SpecificGroups.SL2.BinaryOddRank

/-!
# Model comparison for the original contrary normalizer branch

Transport the actual proper A₆ section from K_vS/O₂(K_vS) into the literal
simple quotient K_v/O₂(K_v). It gives three-rank at least two, order greater
than360, and a factor five. These exclude the rank-one and SL₃ rows of B.5.1,
the small alternating and derived binary rows, and the triple cover of A₆.
The previously proved A₇ centralizer contradiction removes A₇.

The full B.5.1 conclusion on the original canonical action therefore leaves
only SL₄(2), SL₅(2), Sp₄(2ⁿ) and G₂(2ⁿ), with n>1 in the last two families.
All alternatives contain actual isomorphisms of the original quotient.
NormalizerRankTwo removes the last two using the original Sylow bound.
Source: Aschbacher--Smith, 12.6.17, printed p.827, and B.5.1, pp.99--103,
combined manuscript of1 March2004.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Transport the proper original A₆ section into the literal K_v two-core quotient. -/
theorem SourceHypothesis.nonsingular_normalizer_component_section
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (he : ¬ Kv (v : G) ≤ M L)
    (hNM : normalizer (Rv T L (v : G) : Set G) ≤ M L) :
    ∃ A : Subgroup (Star (Kv (v : G))), A ≠ ⊤ ∧
      Nonempty ((A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨S,hTS,_⟩ := exists_sylow_with_Lv_normalizer T L
    H.chosen.sylow_normalizes_component (v : G)
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let C := Kv (v : G)
  let J := C ⊔ S₀
  let C₀ := C.subgroupOf J
  let A := starImage J (Lv L (v : G))
  let B := starImage J C
  have hJG : J ≤ Gv (v : G) := sup_le (Kv_le_Gv _) (map_subtype_le _)
  have hc : C₀.IsCComponent :=
    (H.nonsingular_canonical_component D v hv).1.subgroupOf_of_le le_sup_left hJG
  let c : C₀ ≃* C := subgroupOfEquivOfLe (show C ≤ J from le_sup_left)
  let e : B ≃* Star C := (cComponentTwoCoreQuotientEquiv hc).symm.trans
    (QuotientGroup.congr _ _ c (pCore_map_iso 2 c))
  obtain ⟨hlt,⟨ea⟩,_⟩ := H.nonsingular_normalizer_local_embedding D v hv hs hi he hNM S hTS
  let a : A.subgroupOf B ≃* A := subgroupOfEquivOfLe hlt.le
  let b := (A.subgroupOf B).equivMapOfInjective e.toMonoidHom e.injective
  refine ⟨(A.subgroupOf B).map e.toMonoidHom,?_,⟨?_⟩⟩
  · intro ht
    have hh : A.subgroupOf B = ⊤ := by
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      rw [ht,map_top_of_surjective e.toMonoidHom e.surjective]
    exact hlt.not_ge (subgroupOf_eq_top.mp hh)
  · exact (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).symm.trans
      ((QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans ea)

/-- The original local section forces cubic rank two and component order greater than 360. -/
theorem SourceHypothesis.nonsingular_normalizer_component_bounds
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (he : ¬ Kv (v : G) ≤ M L)
    (hNM : normalizer (Rv T L (v : G) : Set G) ≤ M L) :
    2 ≤ primeRank 3 (Star (Kv (v : G))) ∧
      360 < Nat.card (Star (Kv (v : G))) ∧ 5 ∣ Nat.card (Star (Kv (v : G))) := by
  obtain ⟨A,hA,⟨e⟩⟩ := H.nonsingular_normalizer_component_section D v hv hs hi he hNM
  have hr : 2 ≤ primeRank 3 A := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 A) pCore_isPGroup,
      primeRank_equiv 3 e]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)
  have hd : 360 ∣ Nat.card A := by
    have hh := card_quotient_dvd_card (pCore 2 A)
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup] at hh
    norm_num [Nat.factorial] at hh ⊢
    exact hh
  refine ⟨hr.trans (Theory.GroupTheory.primeRank_le_of_injective 3 A.subtype A.subtype_injective),?_,
    (show 5 ∣ 360 by decide).trans (hd.trans A.card_subgroup_dvd_card)⟩
  have hlt : Nat.card A < Nat.card (Star (Kv (v : G))) := by
    exact lt_of_le_of_ne (card_le_card_group A) (fun hh => hA (A.eq_top_of_card_eq hh))
  exact (Nat.le_of_dvd Nat.card_pos hd).trans_lt hlt

/-- Binary rank one and centerless binary SL₃ are incompatible with the original A₆ section. -/
theorem SourceHypothesis.nonsingular_normalizer_linear_exclusions
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (he : ¬ Kv (v : G) ≤ M L)
    (hNM : normalizer (Rv T L (v : G) : Set G) ≤ M L)
    (F : ChapterB.QuasisimpleSource.BinaryField) :
    ¬ Nonempty (Star (Kv (v : G)) ≃* SL(2,F.Carrier)) ∧
      ¬ Nonempty (Star (Kv (v : G)) ≃* SL(3,F.Carrier)) := by
  have hr := (H.nonsingular_normalizer_component_bounds D v hv hs hi he hNM).1
  constructor
  · rintro ⟨e⟩
    have hb := Matrix.SL2.binary_odd_primeRank_le_one (F := F.Carrier) (by decide : Odd 3)
    rw [primeRank_equiv 3 e] at hr
    omega
  · rintro ⟨e⟩
    let : IsSimpleGroup (Star (Kv (v : G))) :=
      (H.nonsingular_canonical_component D v hv).2.2.2.2
    let : IsQuasisimple (Star (Kv (v : G))) :=
      (H.nonsingular_canonical_component D v hv).2.2.2.1
    let : IsSimpleGroup SL(3,F.Carrier) := e.symm.isSimpleGroup
    let : IsQuasisimple SL(3,F.Carrier) := IsQuasisimple.of_mulEquiv e
    have hz : center SL(3,F.Carrier) = ⊥ := by
      rcases (inferInstance : (center SL(3,F.Carrier)).Normal).eq_bot_or_eq_top with hz | hz
      · exact hz
      · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp hz)).elim
    have hb := Matrix.SL3.binary_threeRank_le_one_of_center_eq_bot F.card_eq hz
    rw [primeRank_equiv 3 e] at hr
    omega
end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open ChapterB.QuasisimpleSource
open scoped MatrixGroups IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The four remaining concrete model families in the contrary branch of 12.6.17. -/
theorem SourceHypothesis.nonsingular_normalizer_models
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hnot : ¬ IsQuasisimple (Kv (v : G)))
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (he : ¬ Kv (v : G) ≤ M L)
    (hNM : normalizer (Rv T L (v : G) : Set G) ≤ M L) :
    Nonempty (Star (Kv (v : G)) ≃* SL(4,ZMod 2)) ∨
      Nonempty (Star (Kv (v : G)) ≃* SL(5,ZMod 2)) ∨
      ∃ F : BinaryField, 1 < F.degree ∧
        (Nonempty (Star (Kv (v : G)) ≃* Matrix.symplecticGroup (Fin 2) F.Carrier) ∨
         Nonempty (Star (Kv (v : G)) ≃* Atlas.G2.Model F.Carrier)) := by
  obtain ⟨S,hTS,hN,hR,hF,hker,hred,hm,hUR,hff⟩ :=
    H.nonsingular_normalizer_canonical_ff D v hv hTV hnot hs hi he hNM
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let J := Kv (v : G) ⊔ S₀
  let E := reducedTwoSubgroup J
  let : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
  let q := ChapterB.InternalThompsonAction.actionMk E
  let ρ := ChapterB.InternalThompsonAction.action E
  let B := ((Kv (v : G)).subgroupOf J).map q
  let O := offenderSubgroup ρ
  let C := B.subgroupOf O
  obtain ⟨_,_,hBO,⟨c⟩⟩ := H.nonsingular_canonical_quasisimple_of_ff D v hv
    S₀ (map_subtype_le _) (S.isPGroup'.map _) hker hff
  obtain ⟨b⟩ := H.nonsingular_canonical_component_image D v hv S₀ (map_subtype_le _) hker
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
  have hb := H.nonsingular_normalizer_component_bounds D v hv hs hi he hNM
  have hsmall {n : ℕ} (hn : n = 5 ∨ n = 6)
      (a : C ≃* alternatingGroup (Fin n)) : False := by
    have hh := hb.2.1
    rw [Nat.card_congr (e.symm.trans a).toEquiv] at hh
    rcases hn with rfl | rfl <;> rw [nat_card_alternatingGroup,Nat.card_fin] at hh <;>
      norm_num [Nat.factorial] at hh
  have hseven (a : C ≃* alternatingGroup (Fin 7)) : False :=
    H.nonsingular_normalizer_not_seven D v hv hs hi he hNM ⟨e.symm.trans a⟩
  have hsp (a : C ≃* commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))) : False := by
    let d := Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm
    let d' : commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)) ≃*
        alternatingGroup (Fin 6) :=
      (d.subgroupMap _).trans (MulEquiv.subgroupCongr (by
        rw [map_commutator_eq,MonoidHom.range_eq_top.mpr d.surjective]
        exact alternatingGroup.commutator_perm_eq (by norm_num)))
    exact hsmall (Or.inr rfl) (a.trans d')
  have hg2 (a : C ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
    have hd := hb.2.2
    rw [Nat.card_congr (e.symm.trans a).toEquiv,
      Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hd
    norm_num at hd
  have height (a : C ≃* alternatingGroup (Fin 8)) :
      Nonempty (Star (Kv (v : G)) ≃* SL(4,ZMod 2)) :=
    ⟨(e.symm.trans a).trans (Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.trans
      (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide : 0 < 4)))⟩
  cases c.clause_one with
  | irreducible _ _ _ hmodel _ =>
    cases hmodel with
    | linearTwo F _ a _ _ =>
      exact ((H.nonsingular_normalizer_linear_exclusions D v hv hs hi he hNM F).1
        ⟨e.symm.trans a.groupEquiv⟩).elim
    | linearThree F _ a _ =>
      exact ((H.nonsingular_normalizer_linear_exclusions D v hv hs hi he hNM F).2
        ⟨e.symm.trans a.groupEquiv⟩).elim
    | symplectic F hn _ a _ => exact .inr (.inr ⟨F,hn,.inl ⟨e.symm.trans a.groupEquiv⟩⟩)
    | symplecticTwo a _ => exact (hsp a.subgroupEquiv).elim
    | g2 F hn _ a _ _ => exact .inr (.inr ⟨F,hn,.inr ⟨e.symm.trans a.groupEquiv⟩⟩)
    | g2Two a _ _ => exact (hg2 a.subgroupEquiv).elim
    | symmetric n hn a _ _ =>
      rcases hn with rfl | rfl
      · exact (hsmall (Or.inl rfl) a.subgroupEquiv).elim
      · exact (hseven a.subgroupEquiv).elim
    | alternatingSix _ a _ _ => exact (hsmall (Or.inr rfl) a.groupEquiv).elim
    | alternatingSeven _ _ a _ _ _ => exact (hseven a).elim
    | tripleSix _ a _ =>
      have hc := Nat.card_congr a.centerEquiv.toEquiv
      change Nat.card (center C) = Nat.card (Multiplicative (ZMod 3)) at hc
      rw [hz,card_bot] at hc
      norm_num at hc
    | binaryLinear d hd _ a _ =>
      rcases hd with rfl | rfl
      · exact .inl ⟨e.symm.trans a.groupEquiv⟩
      · exact .inr (.inl ⟨e.symm.trans a.groupEquiv⟩)
    | orthogonalSix _ _ a _ _ => exact .inl (height a.groupEquiv)
    | symmetricEight _ a _ => exact .inl (height a.subgroupEquiv)
    | exteriorFive _ _ a _ _ _ => exact .inr (.inl ⟨e.symm.trans a⟩)
  | doubleThree F _ a _ _ =>
    exact ((H.nonsingular_normalizer_linear_exclusions D v hv hs hi he hNM F).2
      ⟨e.symm.trans a.groupEquiv⟩).elim
  | naturalDual d hd _ hn =>
    obtain ⟨a⟩ := hn
    rcases hd with rfl | rfl
    · exact .inl ⟨e.symm.trans a.groupEquiv⟩
    · exact .inr (.inl ⟨e.symm.trans a.groupEquiv⟩)
  | repeatedNatural d _ hd _ _ _ hn =>
    obtain ⟨a⟩ := hn
    rcases hd with rfl | rfl
    · exact .inl ⟨e.symm.trans a.groupEquiv⟩
    · exact .inr (.inl ⟨e.symm.trans a.groupEquiv⟩)
end CFSG.Quasithin.Chapter12.Section06
