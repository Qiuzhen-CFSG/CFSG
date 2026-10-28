module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.Local
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceExclusion
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CPU
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.Local
public import Theory.GroupTheory.PRadicalSylowNormalizer
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Local radicality before the exchanged-component classification

Let R=O₂(XU) and let L be the selected C-component in the actual product
K=LLʳ. Distinct C-components normalize one another, so X≤K normalizes L.
The source Sylow subgroup restricts to L R. Thus O₂(N_{LR}(R)) lies in U
and is normalized by X. The actual section-kernel identity for R puts this
two-group in R. This proves the normalized-component consequence of C.2.2(3)
needed by the source C.2.7 and C.1.34 applications, without assuming a block.

Source: Aschbacher–Smith, C.2.2(3), printed p.144, and the characteristic-two
paragraph of 15.4.20, printed p.1164.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases
universe u
variable {G : Type u} [Group G] [Finite G]
variable {d : Source.Geometry G} {i j : Bool} {H U K K₁ : Subgroup G} {r : G}

omit [Finite G] in
private theorem core_normalized (D : Subgroup G) :
    D ≤ normalizer (D.pCoreIn 2 : Set G) :=
  D.le_normalizer.trans (normalizer_le_normalizer_characteristic_image D (pCore 2 D))

/-- The actual product of the two exchanged C-components normalizes the
selected component, hence so does the source X which generates K normally. -/
theorem source_whole_normalizes_selected (h : Input d i j H U K)
    (s : Selected H U K K₁ r) : d.wholeX ≤ normalizer (K₁ : Set G) := by
  have hXK : d.wholeX ≤ K := h.closure ▸
    EmbeddingReduction.le_normalClosureIn h.placed.whole_le
  have hUH : U ≤ H := h.placed.sylow_image ▸ map_subtype_le _
  have hnormal : K ≤ normalizer (K₁ : Set G) := by
    rw [← s.join_eq]
    apply sup_le K₁.le_normalizer
    apply (le_iSup (fun a : U => K₁.map (MulAut.conj (a : G)).toMonoidHom)
      ⟨r, s.conjugator_mem⟩).trans
    exact Chapter1.XiEmbedding.cComponentOrbit_le_normalizer s.component hUH
  exact hXK.trans hnormal

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

private theorem selected_product_sylow (h : Input d i j H U K)
    (s : Selected H U K K₁ r)
    (hn : (sourceRadical d U).subgroupOf H ≤ normalizer (K₁.subgroupOf H : Set H)) :
    Chapter1.IsSylowIn 2 (U ⊓ (K₁ ⊔ sourceRadical d U)) (K₁ ⊔ sourceRadical d U) := by
  obtain ⟨S, hS⟩ := SL3Geometry.source_local_sylow h s hn
  have hRH : sourceRadical d U ≤ H :=
    h.radical_le_sylow.trans (h.placed.sylow_image ▸ map_subtype_le _)
  have hs : Chapter1.IsSylowIn 2
      ((h.placed.sylow : Subgroup H) ⊓ (K₁.subgroupOf H ⊔ (sourceRadical d U).subgroupOf H))
      (K₁.subgroupOf H ⊔ (sourceRadical d U).subgroupOf H) := ⟨S, hS⟩
  have hm := (Chapter1.IsSylowIn.map_iff H.subtype H.subtype_injective).2 hs
  simpa only [Subgroup.map_inf _ _ _ H.subtype_injective, Subgroup.map_sup, map_subgroupOf_eq_of_le s.component.1,
    map_subgroupOf_eq_of_le hRH, h.placed.sylow_image] using hm

private theorem selected_normalizer_core (h : Input d i j H U K)
    (s : Selected H U K K₁ r)
    (hn : (sourceRadical d U).subgroupOf H ≤ normalizer (K₁.subgroupOf H : Set H)) :
    ((K₁ ⊔ sourceRadical d U) ⊓ normalizer (sourceRadical d U : Set G)).pCoreIn 2 =
      sourceRadical d U := by
  let R := sourceRadical d U
  let D := K₁ ⊔ R
  let N := D ⊓ normalizer (R : Set G)
  have hUR : U ≤ normalizer (R : Set G) := le_sup_right.trans (core_normalized _)
  have hXR : d.wholeX ≤ normalizer (R : Set G) := le_sup_left.trans (core_normalized _)
  have hXD : d.wholeX ≤ normalizer (D : Set G) :=
    (le_inf (source_whole_normalizes_selected h s) hXR).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  obtain ⟨S, hS⟩ := selected_product_sylow h s hn
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

/-- The actual contrary radical is radical in the selected component product;
no module or block classification is required. -/
theorem source_radical_in_selected_product (h : Input d i j H U K)
    (s : Selected H U K K₁ r)
    (hn : (sourceRadical d U).subgroupOf H ≤ normalizer (K₁.subgroupOf H : Set H)) :
    IsPRadical 2 ((sourceRadical d U).subgroupOf (K₁ ⊔ sourceRadical d U)) := by
  let R := sourceRadical d U
  let D := K₁ ⊔ R
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
      selected_normalizer_core h s hn, map_subgroupOf_eq_of_le le_sup_right]

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
theorem source_local_radical (h : Input d i j H U K)
    (s : Selected H U K K₁ r)
    (hn : (sourceRadical d U).subgroupOf H ≤ normalizer (K₁.subgroupOf H : Set H)) :
    IsPRadical 2 (((sourceRadical d U).subgroupOf H).subgroupOf
      (K₁.subgroupOf H ⊔ (sourceRadical d U).subgroupOf H)) := by
  have hRH : sourceRadical d U ≤ H :=
    h.radical_le_sylow.trans (h.placed.sylow_image ▸ map_subtype_le _)
  rw [← subgroupOf_sup s.component.1 hRH]
  exact radical_subgroupOf_subgroupOf (sup_le s.component.1 hRH)
    (source_radical_in_selected_product h s hn)

/-- The source SL₃ branch is impossible using the complete earlier C.1.34
implication. The actual configuration supplies local radicality and the
binary component model; neither remains an extra hypothesis. -/
theorem not_source_SL3_branch
    (classification : SL3Geometry.SourceCases.UniversalClassification.{u})
    (h : Input d i j H U K) (s : Selected H U K K₁ r) (κ : GroupClass.{u})
    (hc : ComponentHypotheses κ H ((sourceRadical d U).subgroupOf H)
      (d.M₁.subgroupOf H) (K₁.subgroupOf H))
    (branch : SL3Geometry.SourceCases.SL3Branch κ (K₁.subgroupOf H)
      ((sourceRadical d U).subgroupOf H) (d.M₁.subgroupOf H)) : False :=
  SL3Geometry.not_source_SL3Branch_of_local_radical classification h s κ hc branch
    (source_local_radical h s hc.normalized)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases
