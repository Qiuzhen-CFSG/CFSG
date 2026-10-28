module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Quotient
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.ThreeSubgroups
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.LocalGroups

/-!
# Lifting the first pairing to both source bounds

The triple-commutator conclusion of (1.7)(i) first applies to the actual
normal closure of the selected seed. Containment of the moving subgroup in
that closure, followed by (4.2)(ii), extends it to V. The fixed preimage B
then satisfies [B,Q] ≤ D: the three-subgroups lemma puts [[B,Q],Ltilde]
in D, and residual commutator idempotence removes this central error.

The seed and its (1.7) hypotheses are explicit in the application theorem.
Their construction is still required for the source-only application.
Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(2), printed p.883.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication
open RankOnePairing

variable {G : Type*} [Group G]

theorem commutator_subgroupOf (S A B : Subgroup G) (hA : A ≤ S) (hB : B ≤ S) :
    ⁅A, B⁆.subgroupOf S = ⁅A.subgroupOf S, B.subgroupOf S⁆ := by
  apply map_injective S.subtype_injective
  rw [map_commutator, map_subgroupOf_eq_of_le hA, map_subgroupOf_eq_of_le hB,
    map_subgroupOf_eq_of_le ((Subgroup.commutator_le_sup A B).trans (sup_le hA hB))]

/-- A fixed-preimage commutator follows from the triple bound, without
assuming that the fixed preimage lies in the seed's normal closure. -/
theorem fixed_bound_of_triple [Finite G] (Q L V Z : Subgroup G)
    [Q.Normal] [L.Normal] [V.Normal] [Z.Normal]
    (hQ : IsPGroup 2 Q) (hL : IsPPerfect 2 L)
    (hZQ : ⁅Z, Q⁆ = ⊥)
    (ht : ⁅V, ⁅Q, L⁆⁆ ≤ Q ⊓ centralizer (L : Set G)) :
    ⁅centralizerModulo V L Z, Q⁆ ≤ Q ⊓ centralizer (L : Set G) := by
  let B := centralizerModulo V L Z
  let D := Q ⊓ centralizer (L : Set G)
  have hB : B.Normal := by
    change (V ⊓ (centralizer (L.map (QuotientGroup.mk' Z) : Set (G ⧸ Z))).comap
      (QuotientGroup.mk' Z)).Normal
    let : (L.map (QuotientGroup.mk' Z)).Normal :=
      Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
    infer_instance
  let := hB
  have hBL : ⁅B, L⁆ ≤ Z := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro l hl b hb
    exact (mem_centralizerModulo_iff.mp hb).2 l hl
  have hrot : ⁅⁅B, Q⁆, L⁆ ≤ D := by
    apply commutator_commutator_le_of_rotate
    · rw [commutator_comm ⁅Q, L⁆]
      exact (commutator_mono inf_le_left le_rfl).trans ht
    · rw [commutator_comm L B]
      exact (commutator_mono hBL le_rfl).trans hZQ.le |>.trans bot_le
  have hKQ : ⁅B, Q⁆ ≤ Q := commutator_le_right _ _
  have hzero : ⁅⁅B, Q⁆, L⁆ = ⊥ := by
    rw [← commutator_isPPerfect_idempotent L ⁅B, Q⁆ hL
      (hQ.to_le hKQ) le_normalizer_of_normal]
    exact le_bot_iff.mp ((commutator_mono hrot le_rfl).trans
      (commutator_eq_bot_iff_le_centralizer.mpr
        (show D ≤ centralizer (L : Set G) from inf_le_right)).le)
  exact le_inf hKQ (commutator_eq_bot_iff_le_centralizer.mp hzero)

variable {M : Type*} [Group M] {L R : Subgroup M}

theorem denominator_eq (a : Vertex R) :
    denominator a = (Q R a).subgroupOf (stabilizer R a) ⊓
      centralizer (pResidual 2 (stabilizer R a) : Set (stabilizer R a)) := by
  ext x
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    intro l hl
    exact Subtype.ext (hx.2 l (mem_map_of_mem _ hl))
  · rintro ⟨hx, hc⟩
    refine ⟨hx, ?_⟩
    rintro _ ⟨l, hl, rfl⟩
    exact congrArg Subtype.val (hc l hl)

theorem Ltilde_subgroupOf (a : Vertex R) :
    (Ltilde R a).subgroupOf (stabilizer R a) = pResidual 2 (stabilizer R a) := by
  exact comap_map_eq_self_of_injective (stabilizer R a).subtype_injective _

variable [Finite M] {source : LocalSource L R} {geometry : Geometry R}

include source in
/-- The global component of the quotient pairing is exactly the image of
the source two-residual. Untilded local residuals are not used here. -/
theorem quotient_component (a : Vertex R) (ha : color R a = false)
    (f : FrameAt a) (flag : SL) :
    component (quotientProjection a f.projection f.natural_section.projection_kernel) flag =
      quotientImage a (Ltilde R a) := by
  let := finite_stabilizer R a
  rw [component, rankOne_parabolic_generation _
    (quotientProjection_surjective a _ f.natural_section.projection_surjective _)
    (quotientProjection_kernel_isPGroup source a ha _ _),
    quotientImage, Ltilde_subgroupOf, quotientMap,
    map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _)]

include source in
/-- Both printed bounds follow from the triple bound at the original vertex. -/
theorem bounds_of_triple (hb : 2 < geometry.b R) (a : Vertex R)
    (ha : color R a = false)
    (ht : ⁅V R a, ⁅Q R a, Ltilde R a⁆⁆ ≤ fixedCore R a) :
    BoundsAt geometry a := by
  let S := stabilizer R a
  let := finite_stabilizer R a
  have hQS : Q R a ≤ S := fun _ hx => hx.1
  have hVS : V R a ≤ S := (geometry.V_le_Q hb a ha).trans hQS
  have hLS : Ltilde R a ≤ S := Ltilde_le_stabilizer a
  have hZS : Z R a ≤ S := Z_le_stabilizer R a
  have hKS : ⁅Q R a, Ltilde R a⁆ ≤ S :=
    (Subgroup.commutator_le_sup _ _).trans (sup_le hQS hLS)
  let := Q_normal R a
  let := geometry.Z_normal a
  let : ((V R a).subgroupOf S).Normal :=
    normal_subgroupOf_of_le_normalizer (V_normalized a)
  have ht' : ⁅(V R a).subgroupOf S,
      ⁅(Q R a).subgroupOf S, pResidual 2 S⁆⁆ ≤ denominator a := by
    rw [← Ltilde_subgroupOf a, ← commutator_subgroupOf S _ _ hQS hLS,
      ← commutator_subgroupOf S _ _ hVS hKS]
    exact fun _ hx => ht hx
  rw [denominator_eq] at ht'
  have hz' : ⁅(Z R a).subgroupOf S, (Q R a).subgroupOf S⁆ = ⊥ := by
    rw [← commutator_subgroupOf S _ _ hZS hQS, geometry.centralizes a ha,
      bot_subgroupOf]
  have hh := fixed_bound_of_triple ((Q R a).subgroupOf S) (pResidual 2 S)
    ((V R a).subgroupOf S) ((Z R a).subgroupOf S)
    (Q_isPGroup R source.two_group source.core_le a ha).comap_subtype
    (isPPerfect_pResidual 2) hz' ht'
  rw [← denominator_eq] at hh
  have hm := map_mono (f := S.subtype) hh
  rw [map_commutator, map_subgroupOf_eq_of_le hQS, denominator,
    map_subgroupOf_eq_of_le (show fixedCore R a ≤ S from inf_le_left.trans hQS)] at hm
  exact ⟨ht, hm⟩

/-- Apply the genuine (1.7)(i) theorem and lift its triple conclusion.
Only the containment of Vcirc in the actual generated quotient is needed;
no containment of the whole B in that subgroup is required. -/
theorem bounds_of_pairing (hb : 2 < geometry.b R) (transfer : NormalizationTransfer R)
    (a : Vertex R) (ha : color R a = false) (f : FrameAt a)
    (flag : SL) (hflag : BinaryWeakBN flag) (i : Bool)
    (seed : Subgroup (LocalQuotient a))
    (d : let := quotientImage_normal a (Z R a) (Z_normalized R a)
         let := quotientImage_normal a (Q R a) (Q_normalized R a)
         SourceData
           (quotientExtension source a ha f.projection
             f.natural_section.projection_surjective f.natural_section.projection_kernel flag hflag)
           i (quotientImage a (Z R a)) (quotientImage a (Q R a)) seed)
    (hfixed : quotientImage a (Z R a) ⊓ centralizer
      (localResidual (localParabolic
        (quotientExtension source a ha f.projection
          f.natural_section.projection_surjective f.natural_section.projection_kernel flag hflag)
        i) : Set (LocalQuotient a)) ≠ ⊥)
    (hspan : quotientImage a (Vcirc R a) ≤ generated seed) : BoundsAt geometry a := by
  let := quotientImage_normal a (Z R a) (Z_normalized R a)
  let := quotientImage_normal a (Q R a) (Q_normalized R a)
  have hp := (theorem_1_7_i d hfixed).2.1
  change ⁅⁅quotientImage a (Q R a),
    component (quotientProjection a f.projection f.natural_section.projection_kernel) flag⁆,
    generated seed⁆ = ⊥ at hp
  rw [quotient_component (source := source) a ha f flag] at hp
  have hQS : Q R a ≤ stabilizer R a := fun _ hx => hx.1
  have hVS : V R a ≤ stabilizer R a := (geometry.V_le_Q hb a ha).trans hQS
  have hLS := Ltilde_le_stabilizer (R := R) a
  have hKS : ⁅Q R a, Ltilde R a⁆ ≤ stabilizer R a :=
    (Subgroup.commutator_le_sup _ _).trans (sup_le hQS hLS)
  have hCS : Vcirc R a ≤ stabilizer R a :=
    (Subgroup.commutator_le_sup _ _).trans (sup_le hVS hLS)
  have hc : ⁅Vcirc R a, ⁅Q R a, Ltilde R a⁆⁆ ≤ fixedCore R a := by
    apply (quotient_commutator_eq_bot_iff a _ _ hCS hKS).mp
    rw [quotientImage_commutator a _ _ hQS hLS, commutator_comm]
    exact le_bot_iff.mp ((commutator_mono le_rfl hspan).trans hp.le)
  have hKQ : ⁅Q R a, Ltilde R a⁆ ≤ Q R a :=
    le_normalizer_iff_commutator_le_left.mp (hLS.trans (Q_normalized R a))
  have hKn : (⁅Q R a, Ltilde R a⁆.subgroupOf (stabilizer R a)).Normal := by
    rw [commutator_subgroupOf _ _ _ hQS hLS, Ltilde_subgroupOf]
    let := Q_normal R a
    infer_instance
  exact bounds_of_triple (source := source) hb a ha (transfer a ha _ hKQ hKn hc)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication
