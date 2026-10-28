module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.SingleComponentInputs
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.LocalRadical

/-!
# Literal star geometry for a single contrary component

For the normal closure K, the actual source X normalizes K and its product
with R=O₂(XU). The normalizer core in KR is normalized by X and lies in U;
the established section-kernel identity therefore puts it in R. This proves
local radicality and identifies the star kernel with O₂(KR). The actual
C-component quotient K/O₂(K) is consequently its image in the star group.
No classified module, kernel equality or quotient model is an input.
Source: Aschbacher--Smith, C.2.2(3), C.2.7 and 15.4.20, pp.144--147,1164.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination
open BlockSieve BlockSieve.ExchangedCases
universe u
variable {G : Type u} [Group G] [Finite G]
variable {d : Source.Geometry G} {i j : Bool} {H U K : Subgroup G}

omit [Finite G] in
private theorem core_normalized (D : Subgroup G) :
    D ≤ normalizer (D.pCoreIn 2 : Set G) :=
  D.le_normalizer.trans (normalizer_le_normalizer_characteristic_image D (pCore 2 D))

omit [Finite G] in
private theorem source_single_le (h : Input d i j H U K) : K ≤ H :=
  h.closure ▸ EmbeddingReduction.normalClosureIn_le_overgroup _ _

omit [Finite G] in
private theorem source_single_normal (h : Input d i j H U K) :
    (K.subgroupOf H).Normal :=
  h.closure ▸ EmbeddingReduction.normalClosureIn_normal _ _

omit [Finite G] in
private theorem source_radical_normalizes_single (h : Input d i j H U K) :
    (sourceRadical d U).subgroupOf H ≤ normalizer (K.subgroupOf H : Set H) := by
  let _ := source_single_normal h
  exact le_normalizer_of_normal

omit [Finite G] in
private theorem source_whole_normalizes_single (h : Input d i j H U K) :
    d.wholeX ≤ normalizer (K : Set G) :=
  h.placed.whole_le.trans ((normal_subgroupOf_iff_le_normalizer (source_single_le h)).mp
    (source_single_normal h))

omit [Finite G] in
private theorem upper_two (h : Input d i j H U K) : IsPGroup 2 U := by
  rw [← h.placed.sylow_image]
  exact h.placed.sylow.isPGroup'.map _

omit [Finite G] in
private theorem normalized_two_le_radical (h : Input d i j H U K)
    (Q : Subgroup G) (hQU : Q ≤ U) (hXQ : d.wholeX ≤ normalizer (Q : Set G)) :
    Q ≤ sourceRadical d U := by
  have hUX : U ≤ normalizer (d.wholeX : Set G) :=
    h.placed.upper.le.trans h.placed.T_normalizes
  have hQcore : Q ⊓ d.wholeX ≤ d.wholeX.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((upper_two h).to_le (inf_le_left.trans hQU)) inf_le_right
      ((le_inf hXQ d.wholeX.le_normalizer).trans inf_normalizer_le_normalizer_inf)
  have hQC : Q ≤ ChapterA.Section04.twoSectionCentralizer d.wholeX (d.wholeX ⊔ U) := by
    apply (ChapterA.Section04.le_twoSectionCentralizer_iff _ _ _).mpr
    refine ⟨hQU.trans le_sup_right, hQU.trans hUX, ?_⟩
    exact (le_inf (le_normalizer_iff_commutator_le_right.mp hXQ)
      (le_normalizer_iff_commutator_le_left.mp (hQU.trans hUX))).trans hQcore
  change Q ≤ (d.wholeX ⊔ U : Subgroup G).pCoreIn 2
  rw [contrary_core_eq_section_kernel le_sup_left le_sup_right
    (sup_le h.placed.whole_le (h.placed.sylow_image ▸ map_subtype_le _))
    (sup_le d.wholeX.le_normalizer hUX) h.placed.sylow h.placed.sylow_image]
  exact le_inf hQU hQC

private theorem single_product_sylow (h : Input d i j H U K) :
    Chapter1.IsSylowIn 2 (U ⊓ (K ⊔ sourceRadical d U)) (K ⊔ sourceRadical d U) := by
  have hn := source_radical_normalizes_single h
  have hRP : (sourceRadical d U).subgroupOf H ≤ (h.placed.sylow : Subgroup H) := by
    intro x hx
    have hxU := h.radical_le_sylow hx
    rw [← h.placed.sylow_image] at hxU
    obtain ⟨y, hy, he⟩ := hxU
    exact (Subtype.ext he : y = x) ▸ hy
  obtain ⟨S, hS⟩ := SL3Geometry.local_sylow h.placed.sylow _ _
    (source_single_normal h).isSubnormal hRP hn
  have hRH : sourceRadical d U ≤ H :=
    h.radical_le_sylow.trans (h.placed.sylow_image ▸ map_subtype_le _)
  have hs : Chapter1.IsSylowIn 2
      ((h.placed.sylow : Subgroup H) ⊓ (K.subgroupOf H ⊔ (sourceRadical d U).subgroupOf H))
      (K.subgroupOf H ⊔ (sourceRadical d U).subgroupOf H) := ⟨S, hS⟩
  have hm := (Chapter1.IsSylowIn.map_iff H.subtype H.subtype_injective).2 hs
  simpa only [Subgroup.map_inf _ _ _ H.subtype_injective, Subgroup.map_sup, map_subgroupOf_eq_of_le (source_single_le h),
    map_subgroupOf_eq_of_le hRH, h.placed.sylow_image] using hm

private theorem single_normalizer_core (h : Input d i j H U K) :
    ((K ⊔ sourceRadical d U) ⊓ normalizer (sourceRadical d U : Set G)).pCoreIn 2 =
      sourceRadical d U := by
  let R := sourceRadical d U
  let D := K ⊔ R
  let N := D ⊓ normalizer (R : Set G)
  have hUR : U ≤ normalizer (R : Set G) := le_sup_right.trans (core_normalized _)
  have hXR : d.wholeX ≤ normalizer (R : Set G) := le_sup_left.trans (core_normalized _)
  have hXD : d.wholeX ≤ normalizer (D : Set G) :=
    (le_inf (source_whole_normalizes_single h) hXR).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  obtain ⟨S, hS⟩ := single_product_sylow h
  have hSN : (S : Subgroup D).map D.subtype ≤ N :=
    hS.le.trans (le_inf inf_le_right (inf_le_left.trans hUR))
  have hQN : N.pCoreIn 2 ≤ U := by
    have hh := pCoreIn_le_sylow N (restrictSylow S inf_le_left hSN)
    rw [restrictSylow_image, hS] at hh
    exact hh.trans inf_le_left
  have hXN : d.wholeX ≤ normalizer (N : Set G) :=
    (le_inf hXD (hXR.trans (normalizer (R : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  apply le_antisymm
  · exact normalized_two_le_radical h _ hQN
      (hXN.trans (normalizer_le_normalizer_characteristic_image N (pCore 2 N)))
  · exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _)
      (le_inf le_sup_right le_normalizer) inf_le_right

/-- The actual contrary radical is radical in the normal component product;
no module or block classification is required. -/
theorem source_radical_in_single_product (h : Input d i j H U K) :
    IsPRadical 2 ((sourceRadical d U).subgroupOf (K ⊔ sourceRadical d U)) := by
  let R := sourceRadical d U
  let D := K ⊔ R
  have hRne : R ≠ ⊥ := by
    intro he
    have hz := h.seed_le_radical
    change d.Z ≤ R at hz
    rw [he] at hz
    have hzbot : d.Z = ⊥ := le_bot_iff.mp hz
    have hc := h.seed_card
    rw [hzbot, card_bot] at hc
    omega
  refine ⟨?_, ?_⟩
  · intro he
    have hm := congrArg (Subgroup.map D.subtype) he
    rw [map_subgroupOf_eq_of_le le_sup_right, Subgroup.map_bot] at hm
    exact hRne hm
  · change (normalizer (R.subgroupOf D : Set D)).pCoreIn 2 = R.subgroupOf D
    apply Subgroup.map_injective D.subtype_injective
    rw [map_pCoreIn_of_injective 2 _ D.subtype D.subtype_injective,
      ← subgroupOf_normalizer_eq (show R ≤ D from le_sup_right),
      subgroupOf_map_subtype, inf_comm (normalizer (R : Set G)) D,
      single_normalizer_core h, map_subgroupOf_eq_of_le le_sup_right]

omit [Finite G] in
private theorem radical_subgroupOf_subgroupOf {R D H : Subgroup G} (hDH : D ≤ H)
    (hrad : IsPRadical 2 (R.subgroupOf D)) :
    IsPRadical 2 ((R.subgroupOf H).subgroupOf (D.subgroupOf H)) := by
  let e := (subgroupOfEquivOfLe hDH).symm
  have hm : (R.subgroupOf D).map e.toMonoidHom =
      (R.subgroupOf H).subgroupOf (D.subgroupOf H) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
  exact hm ▸ hrad.map_equiv e

/-- The local radical statement with the exact nested subgroup convention
used by the C.2.7 and C.1.34 source consumers. -/
theorem single_local_radical (h : Input d i j H U K) :
    IsPRadical 2 (((sourceRadical d U).subgroupOf H).subgroupOf
      (K.subgroupOf H ⊔ (sourceRadical d U).subgroupOf H)) := by
  have hRH : sourceRadical d U ≤ H :=
    h.radical_le_sylow.trans (h.placed.sylow_image ▸ map_subtype_le _)
  rw [← subgroupOf_sup (source_single_le h) hRH]
  exact radical_subgroupOf_subgroupOf (sup_le (source_single_le h) hRH)
    (source_radical_in_single_product h)

private noncomputable def quotientImageEquiv
    {D : Type u} [Group D] [Finite D] (L : Subgroup D) (hL : L.IsCComponent)
    (N : Subgroup D) [N.Normal] (hN : N = pCore 2 D) :
    (L ⧸ pCore 2 L) ≃* L.map (QuotientGroup.mk' N) := by
  subst N
  exact cComponentTwoCoreQuotientEquiv hL

/-- The source single component has exactly its original core quotient in
C.2.7's literal star group. Local radicality and the star kernel are proved. -/
noncomputable def single_componentStarEquiv (h : Input d i j H U K)
    (hK : (K.subgroupOf H).IsCComponent) :
    Chapter1.XiQuotient K ≃* SL3Geometry.SourceCases.starComponent
      (K.subgroupOf H) ((sourceRadical d U).subgroupOf H) := by
  let L := K.subgroupOf H
  let R := (sourceRadical d U).subgroupOf H
  let D := L ⊔ R
  let e := (subgroupOfEquivOfLe (show L ≤ D from le_sup_left)).symm
  let eH := (subgroupOfEquivOfLe (source_single_le h)).symm
  let eQ : Chapter1.XiQuotient K ≃* ((L.subgroupOf D) ⧸ pCore 2 (L.subgroupOf D)) :=
    (QuotientGroup.congr _ _ eH (pCore_map_iso 2 eH)).trans
      (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
  have hk := SL3Geometry.SourceCases.source_starKernel_eq_core h L
    (source_radical_normalizes_single h) (single_local_radical h)
  exact eQ.trans (quotientImageEquiv (L.subgroupOf D) (hK.subgroupOf le_sup_left)
    (SL3Geometry.SourceCases.starKernel L R) hk)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination
