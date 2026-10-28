module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.CanonicalSection
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.NormalizerRankTwo

/-!
# The remaining canonical FF component models

The proper original A6 section forces cubic rank two, order greater than
360 and a factor five. These exclude binary rank one, binary SL3, the
small alternating and derived binary rows of B.5.1. Centerlessness excludes
the triple cover. The original index-four Sylow geometry excludes the
nonbinary Sp4 and G2 rows. Thus the literal K_v/O2(K_v) is A7, SL4(2),
or SL5(2), provided its canonical action is FF.

The FF premise is explicit: this is the model-comparison step of 12.6.18,
not a proof of 12.6.15. PreferredCanonical supplies the same-point section
and kernel and retains the FF obligation with this source assembly.
Neither 12.6.2 nor 12.6.23 is asserted. Source: Aschbacher--Smith,
12.6.15 and 12.6.18, printed pp.826--827, and B.5.1, pp.99--103,
combined manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
/-- Binary rank one and centerless binary SL₃ are incompatible with the original A₆ section. -/
theorem SourceHypothesis.nonsingular_canonical_linear_exclusions
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (he : ¬ Kv (v : G) ≤ M L)
    (S : Sylow 2 (Gv (v : G)))
    (hRN : R L (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) (v : G) ≤
      normalizer (Lv L (v : G) : Set G))
    (F : ChapterB.QuasisimpleSource.BinaryField) :
    ¬ Nonempty (Star (Kv (v : G)) ≃* SL(2,F.Carrier)) ∧
      ¬ Nonempty (Star (Kv (v : G)) ≃* SL(3,F.Carrier)) := by
  have hr := (H.nonsingular_canonical_component_bounds D v hv he S hRN).1
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

/-- The original FF action leaves only A7, SL4(2), and SL5(2), with actual quotient equivalences. -/
theorem SourceHypothesis.nonsingular_canonical_ff_models
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (he : ¬ Kv (v : G) ≤ M L)
    (S : Sylow 2 (Gv (v : G)))
    (hRN : R L (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) (v : G) ≤
      normalizer (Lv L (v : G) : Set G))
    (hker : centralizer (reducedTwoSubgroup (Kv (v : G) ⊔
      (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G) :
      Set (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G)) =
        pCore 2 (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G))
    (hff : let E := reducedTwoSubgroup (Kv (v : G) ⊔
      (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G)
      letI : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
      IsFFModule (ChapterB.InternalThompsonAction.action E)) :
    Nonempty (Star (Kv (v : G)) ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (Star (Kv (v : G)) ≃* SL(4,ZMod 2)) ∨
      Nonempty (Star (Kv (v : G)) ≃* SL(5,ZMod 2)) := by
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
  have hb := H.nonsingular_canonical_component_bounds D v hv he S hRN
  have hsmall {n : ℕ} (hn : n = 5 ∨ n = 6)
      (a : C ≃* alternatingGroup (Fin n)) : False := by
    have hh := hb.2.1
    rw [Nat.card_congr (e.symm.trans a).toEquiv] at hh
    rcases hn with rfl | rfl <;> rw [nat_card_alternatingGroup,Nat.card_fin] at hh <;>
      norm_num [Nat.factorial] at hh
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
      exact ((H.nonsingular_canonical_linear_exclusions D v hv he S hRN F).1
        ⟨e.symm.trans a.groupEquiv⟩).elim
    | linearThree F _ a _ =>
      exact ((H.nonsingular_canonical_linear_exclusions D v hv he S hRN F).2
        ⟨e.symm.trans a.groupEquiv⟩).elim
    | symplectic F hn _ a _ =>
      exact ((H.nonsingular_canonical_rankTwo_exclusions D v hv hTV hi F hn).1
        ⟨e.symm.trans a.groupEquiv⟩).elim
    | symplecticTwo a _ => exact (hsp a.subgroupEquiv).elim
    | g2 F hn _ a _ _ =>
      exact ((H.nonsingular_canonical_rankTwo_exclusions D v hv hTV hi F hn).2
        ⟨e.symm.trans a.groupEquiv⟩).elim
    | g2Two a _ _ => exact (hg2 a.subgroupEquiv).elim
    | symmetric n hn a _ _ =>
      rcases hn with rfl | rfl
      · exact (hsmall (Or.inl rfl) a.subgroupEquiv).elim
      · exact .inl ⟨e.symm.trans a.subgroupEquiv⟩
    | alternatingSix _ a _ _ => exact (hsmall (Or.inr rfl) a.groupEquiv).elim
    | alternatingSeven _ _ a _ _ _ => exact .inl ⟨e.symm.trans a⟩
    | tripleSix _ a _ =>
      have hc := Nat.card_congr a.centerEquiv.toEquiv
      change Nat.card (center C) = Nat.card (Multiplicative (ZMod 3)) at hc
      rw [hz,card_bot] at hc
      norm_num at hc
    | binaryLinear d hd _ a _ =>
      rcases hd with rfl | rfl
      · exact .inr (.inl ⟨e.symm.trans a.groupEquiv⟩)
      · exact .inr (.inr ⟨e.symm.trans a.groupEquiv⟩)
    | orthogonalSix _ _ a _ _ => exact .inr (.inl (height a.groupEquiv))
    | symmetricEight _ a _ => exact .inr (.inl (height a.subgroupEquiv))
    | exteriorFive _ _ a _ _ _ => exact .inr (.inr ⟨e.symm.trans a⟩)
  | doubleThree F _ a _ _ =>
    exact ((H.nonsingular_canonical_linear_exclusions D v hv he S hRN F).2
      ⟨e.symm.trans a.groupEquiv⟩).elim
  | naturalDual d hd _ hn =>
    obtain ⟨a⟩ := hn
    rcases hd with rfl | rfl
    · exact .inr (.inl ⟨e.symm.trans a.groupEquiv⟩)
    · exact .inr (.inr ⟨e.symm.trans a.groupEquiv⟩)
  | repeatedNatural d _ hd _ _ _ hn =>
    obtain ⟨a⟩ := hn
    rcases hd with rfl | rfl
    · exact .inr (.inl ⟨e.symm.trans a.groupEquiv⟩)
    · exact .inr (.inr ⟨e.symm.trans a.groupEquiv⟩)

end CFSG.Quasithin.Chapter12.Section06
