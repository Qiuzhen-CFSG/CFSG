module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.Components.Placement
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.Marking
public import Theory.GroupTheory.CComponent.SimplePairProduct
public import Theory.GroupTheory.PCoreInRestriction
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Ordered product and odd-index residual from the two relative components

Recognition of K and L₂ as relative C-components supplies normality through
unique containment. Their distinct simple two-core quotients give an ordered
product projection with kernel exactly P. Comparing the unipotent subgroup
of that product with |P| and |T| puts the original T in K∨L₂. Hence the
literal Y=⟨L₂, I⟩ equals K∨L₂ and O^{2′}(G_P), and the projection gives a
marking of the actual quotient Y/P.

The field equivalence here identifies the factor groups only. No agreement
of the independent natural module structures is assumed. The two component
premises remain to be proved by the common-core orthogonal owner before
this conditional theorem family can complete the source paragraph.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004, printed p.774.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore

private theorem marked_pair_projection {J E F : Type*} [Group J] [Finite J]
    [Group E] [Group F] [IsSimpleGroup E] [IsSimpleGroup F]
    (B C P : Subgroup J) [C.Normal]
    (hB : B.IsCComponent) (hC : C.IsCComponent) (hne : B ≠ C)
    (hgen : B ⊔ C = ⊤) (hBP : B.pCoreIn 2 = P) (hCP : C.pCoreIn 2 = P)
    (eB : (B ⧸ pCore 2 B) ≃* E) (eC : (C ⧸ pCore 2 C) ≃* F) :
    ∃ q : J →* E × F, Function.Surjective q ∧ q.ker = P ∧
      B.map q = (MonoidHom.snd E F).ker ∧ C.map q = (MonoidHom.fst E F).ker := by
  obtain ⟨q, hq, _hker, hb, hc⟩ := exists_twoCore_product_of_simple_pair B C hB hC hne hgen eB eC
  have hb0 (b : B) : q b = 1 ↔ (b : J) ∈ P := by
    rw [hb]
    change (eB (QuotientGroup.mk' _ b), 1) = (1, 1) ↔ _
    simp only [Prod.mk.injEq, and_true]
    rw [map_eq_one_iff eB eB.injective,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← hBP]
    exact (mem_map_iff_mem B.subtype_injective).symm
  have hc0 (c : C) : q c = 1 ↔ (c : J) ∈ P := by
    rw [hc]
    change (1, eC (QuotientGroup.mk' _ c)) = (1, 1) ↔ _
    simp only [Prod.mk.injEq, true_and]
    rw [map_eq_one_iff eC eC.injective,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← hCP]
    exact (mem_map_iff_mem C.subtype_injective).symm
  refine ⟨q, hq, ?_, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨b, hb', c, hc', he⟩ := mem_sup_of_normal_right.mp (hgen ▸ mem_top x)
      have h := show q x = 1 from hx
      rw [← he, map_mul, hb ⟨b, hb'⟩, hc ⟨c, hc'⟩] at h
      have h1 : q b = 1 := by
        rw [hb ⟨b, hb'⟩]
        exact Prod.ext (by simpa using congrArg Prod.fst h) rfl
      have h2 : q c = 1 := by
        rw [hc ⟨c, hc'⟩]
        exact Prod.ext rfl (by simpa using congrArg Prod.snd h)
      rw [← he]
      exact P.mul_mem ((hb0 ⟨b, hb'⟩).mp h1) ((hc0 ⟨c, hc'⟩).mp h2)
    · intro hx
      exact (hb0 ⟨x, (hBP ▸ B.pCoreIn_le 2) hx⟩).mpr hx
  · ext x
    constructor
    · rintro ⟨b, hb', rfl⟩
      change (q b).2 = 1
      rw [hb ⟨b, hb'⟩]
    · intro hx
      obtain ⟨b, hb'⟩ := (eB.surjective.comp (QuotientGroup.mk'_surjective _)) x.1
      refine ⟨b, b.property, ?_⟩
      rw [hb]
      exact Prod.ext hb' (show x.2 = 1 from hx).symm
  · ext x
    constructor
    · rintro ⟨c, hc', rfl⟩
      change (q c).1 = 1
      rw [hc ⟨c, hc'⟩]
    · intro hx
      obtain ⟨c, hc'⟩ := (eC.surjective.comp (QuotientGroup.mk'_surjective _)) x.2
      refine ⟨c, c.property, ?_⟩
      rw [hc]
      exact Prod.ext (show x.1 = 1 from hx).symm hc'

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H X A : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)}
    {f : InvariantFlag (.sl3 m)} {h : G}
    (d : OrthogonalInput D S m f H X A h)
include d

/-- Component recognition supplies relative normality through the unique
normal containing components already constructed in the local family. -/
theorem source_factors_normal_of_components
    (hK : Source.ComponentIn (coreNormalizer V H h) (outsideResidual H))
    (hL : Source.ComponentIn (coreNormalizer V H h) (f.Li 1)) :
    ((outsideResidual H).subgroupOf (coreNormalizer V H h)).Normal ∧
      ((f.Li 1).subgroupOf (coreNormalizer V H h)).Normal := by
  obtain ⟨K, hKplus, _, huK⟩ := source_residual_containing_component d
  obtain ⟨J, hJplus, _, huJ⟩ := source_local_containing_component d
  exact ⟨huK _ hK le_rfl ▸ hKplus.2, huJ _ hL le_rfl ▸ hJplus.2⟩

/-- The ordered factors of the literal quotient of K∨L₂ by P. The finite
field equivalence is used only to identify the groups; it asserts no
compatibility between the two natural module structures. -/
theorem source_factorJoin_product_of_components
    (hK : Source.ComponentIn (coreNormalizer V H h) (outsideResidual H))
    (hL : Source.ComponentIn (coreNormalizer V H h) (f.Li 1)) :
    Nonempty (ProductQuotientMarking (outsideResidual H ⊔ f.Li 1)
      (pairCore V H h) (outsideResidual H) (f.Li 1) S.field) := by
  let J := outsideResidual H ⊔ f.Li 1
  have hJG : J ≤ coreNormalizer V H h := sup_le hK.1 hL.1
  have hn := source_factors_normal_of_components d hK hL
  have hln : coreNormalizer V H h ≤ normalizer (f.Li 1 : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hL.1).mp hn.2
  let B := (outsideResidual H).subgroupOf J
  let C := (f.Li 1).subgroupOf J
  let P := (pairCore V H h).subgroupOf J
  let : C.Normal := normal_subgroupOf_of_le_normalizer (hJG.trans hln)
  have hb : B.IsCComponent := hK.2.subgroupOf_of_le le_sup_left hJG
  have hc : C.IsCComponent := hL.2.subgroupOf_of_le le_sup_right hJG
  have hne : B ≠ C := by
    intro he
    have hh := congrArg (map J.subtype) he
    rw [map_subgroupOf_eq_of_le (show outsideResidual H ≤ J from le_sup_left),
      map_subgroupOf_eq_of_le (show f.Li 1 ≤ J from le_sup_right)] at hh
    exact source_residual_ne_local d hh
  have hgen : B ⊔ C = ⊤ := by
    rw [← subgroupOf_sup (show outsideResidual H ≤ J from le_sup_left)
      (show f.Li 1 ≤ J from le_sup_right)]
    exact subgroupOf_self J
  have hbP : B.pCoreIn 2 = P := by
    rw [pCoreIn_subgroupOf _ _ _ le_sup_left, d.residual_core]
  have hcP : C.pCoreIn 2 = P := by
    rw [pCoreIn_subgroupOf _ _ _ le_sup_right, d.local_core]
  let : Fintype d.pair_field.Carrier := Fintype.ofFinite _
  let : Fintype S.field.Carrier := Fintype.ofFinite _
  let ef : d.pair_field.Carrier ≃+* S.field.Carrier := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      d.pair_field.card_eq, S.field.card_eq, d.pair_degree])
  let b := subgroupOfEquivOfLe (show outsideResidual H ≤ J from le_sup_left)
  let c := subgroupOfEquivOfLe (show f.Li 1 ≤ J from le_sup_right)
  let eB : (B ⧸ pCore 2 B) ≃* SL(2, S.field.Carrier) :=
    (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans
      (d.pair_natural.quotientEquiv.trans (GorensteinWalter.sl2RingEquiv ef))
  let eC : (C ⧸ pCore 2 C) ≃* SL(2, S.field.Carrier) :=
    (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans
      ((SL3.flagLocalCoreEquiv S m f 1).trans
        (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := S.field.Carrier)).symm)
  let : IsSimpleGroup PSL(2, S.field.Carrier) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      rw [S.field.card_eq]
      exact (show (4 : ℕ) = 2 ^ 2 from rfl).le.trans
        (Nat.pow_le_pow_right (by decide) S.nonbinary))
  let : IsSimpleGroup SL(2, S.field.Carrier) :=
    (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := S.field.Carrier)).isSimpleGroup
  obtain ⟨q, hq, hker, hfirst, hsecond⟩ := marked_pair_projection B C P hb hc hne hgen hbP hcP eB eC
  exact ⟨{
    core_le := (source_pairCore_le_factors d).1.trans le_sup_left
    first_le := le_sup_left
    second_le := le_sup_right
    normalizes := hJG
    projection := q
    surjective := hq
    kernel := hker
    first_factor := hfirst
    second_factor := hsecond }⟩

omit d in
private theorem sylow_le_normalized_of_card_dvd (R : Sylow 2 G) (J : Subgroup G)
    (hn : (R : Subgroup G) ≤ normalizer (J : Set G))
    (hd : Nat.card R ∣ Nat.card J) : (R : Subgroup G) ≤ J := by
  obtain ⟨U, hU⟩ := NormalSylowQuotientAction.intersection_sylow R J hn
  obtain ⟨k, hk⟩ := R.isPGroup'.exists_card_eq
  have hdU : Nat.card R ∣ Nat.card U := by
    rw [hk] at hd ⊢
    exact U.pow_dvd_card_of_pow_dvd_card hd
  have hmap : (U : Subgroup J).map J.subtype = (R : Subgroup G) ⊓ J := by
    rw [hU, subgroupOf_map_subtype, inf_comm]
  have hcard : Nat.card ↥((R : Subgroup G) ⊓ J) = Nat.card U := by
    rw [← hmap, card_map_of_injective J.subtype_injective]
  have he : (R : Subgroup G) ⊓ J = R := eq_of_le_of_card_ge inf_le_left (by
    rw [hcard]
    exact Nat.le_of_dvd Nat.card_pos hdU)
  exact inf_eq_left.mp he

/-- The original Sylow lies in K∨L₂. The ordered quotient contains a
unipotent subgroup of order q², and P has order q⁴, exhausting |T|=q⁶. -/
theorem source_sylow_le_factorJoin_of_components
    (hK : Source.ComponentIn (coreNormalizer V H h) (outsideResidual H))
    (hL : Source.ComponentIn (coreNormalizer V H h) (f.Li 1)) :
    (T : Subgroup G) ≤ outsideResidual H ⊔ f.Li 1 := by
  obtain ⟨a⟩ := source_factorJoin_product_of_components d hK hL
  let J := outsideResidual H ⊔ f.Li 1
  have hn := source_factors_normal_of_components d hK hL
  have hkn := (normal_subgroupOf_iff_le_normalizer hK.1).mp hn.1
  have hln := (normal_subgroupOf_iff_le_normalizer hL.1).mp hn.2
  have hTJ : (T : Subgroup G) ≤ normalizer (J : Set G) :=
    (sylow_le_coreNormalizer f d.local_core).trans
      ((le_inf hkn hln).trans (normalizer_inf_normalizer_le_normalizer_sup _ _))
  apply sylow_le_normalized_of_card_dvd T J hTJ
  let := a.coreNormal
  have hcard : Nat.card J =
      Nat.card (SL(2, S.field.Carrier) × SL(2, S.field.Carrier)) * (2 ^ S.field.degree) ^ 4 := by
    rw [card_eq_card_quotient_mul_card_subgroup ((pairCore V H h).subgroupOf J),
      Nat.card_congr a.quotientEquiv.toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe a.core_le).toEquiv, source_pairCore_card d]
  have hdiv : (2 ^ S.field.degree) ^ 2 ∣
      Nat.card (SL(2, S.field.Carrier) × SL(2, S.field.Carrier)) := by
    let U := Matrix.SpecialLinearGroup.upperUnipotent S.field.Carrier
    have hu : Nat.card (U.prod U) = (2 ^ S.field.degree) ^ 2 := by
      rw [Nat.card_congr (prodEquiv U U).toEquiv, Nat.card_prod,
        Matrix.SpecialLinearGroup.card_upperUnipotent, S.field.card_eq, pow_two]
    exact hu ▸ (U.prod U).card_subgroup_dvd_card
  rw [source_sylow_card d (source_original_sylow_placement d).2.1, hcard]
  have hpow : (2 ^ S.field.degree) ^ 6 =
      (2 ^ S.field.degree) ^ 2 * (2 ^ S.field.degree) ^ 4 := by rw [← pow_add]
  rw [hpow]
  exact Nat.mul_dvd_mul_right hdiv _

/-- With the two component assertions supplied, the original join equals
the product of those factors and is the odd-index residual of G_P. -/
theorem source_factorJoin_and_residual_of_components
    (hK : Source.ComponentIn (coreNormalizer V H h) (outsideResidual H))
    (hL : Source.ComponentIn (coreNormalizer V H h) (f.Li 1)) :
    orthogonalJoin (f.Li 1) V h = outsideResidual H ⊔ f.Li 1 ∧
      orthogonalJoin (f.Li 1) V h =
        (primeToResidual 2 (coreNormalizer V H h)).map (coreNormalizer V H h).subtype := by
  have hT := source_sylow_le_factorJoin_of_components d hK hL
  have hn := source_factors_normal_of_components d hK hL
  exact ⟨source_orthogonalJoin_eq_factorJoin d hT,
    source_orthogonalJoin_eq_oddResidual_of_normal_factors d hn.1 hn.2 hT⟩

/-- The actual Y/P receives the ordered product marking. No Sylow,
normality, or residual premise remains besides recognition of K and L₂
as relative C-components; final discharge belongs to this task. -/
theorem source_product_quotient_of_components
    (hK : Source.ComponentIn (coreNormalizer V H h) (outsideResidual H))
    (hL : Source.ComponentIn (coreNormalizer V H h) (f.Li 1)) :
    Nonempty (ProductQuotientMarking (orthogonalJoin (f.Li 1) V h)
      (pairCore V H h) (outsideResidual H) (f.Li 1) S.field) := by
  rw [(source_factorJoin_and_residual_of_components d hK hL).1]
  exact source_factorJoin_product_of_components d hK hL

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
