module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Setup
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Detection.Contracts
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Detection.CommutingProduct
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Detection.FactorCentralizers
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Detection.CentralizerProduct

/-!
# Detecting a genuine block in the characteristic-two envelope

E.6.7 is applied to the actual characteristic-two envelope. A factor
centralizing U lifts through the normal layer centralizer and restricts
to a genuine block of C_G(U). Exact C.1.9 applies there, since E.6.21
discharges its additional O₂,₃ hypothesis. The centralizing-product
lemma then identifies the original escaping block with one of these
factors. Its literal module and its relative subnormality in the envelope
are consequently supplied by that factor of E.6.7.

The final theorem discharges the centralizer product using the actual
E.6.7 factor transporters. Its remaining explicit inputs are exact E.6.7,
exact C.1.9, odd-core freeness, and characteristic two for hyperplane
centralizers. Layer placement is retained locally in the detection
contract. Neither block persistence nor factor identification is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.7,
printed p.246, E.6.23, printed pp.254–255, and C.1.7–13, pp.123–125.
-/

public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three
open InvariantSubspaces.BlockSelection Detection

variable {G : Type*} [Group G] [Finite G] {M V : Subgroup G}

/-- The original block is a literal envelope factor once the centralizer
product is known. All block comparisons take place in C_G(U). -/
theorem envelope_factor_of_centralizerProduct
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (h19 : BlockCommutationInput G) (h21 : OddCoreFree V)
    (hprod : EnvelopeCentralizerProduct T M V)
    {U A L : Subgroup G} (hU : U ∈ obstructionFamily M V)
    (hUh : IsHyperplane V U) (hL : SmallBlock U L) (he : ¬ L ≤ M)
    (hA : A ∈ obstructionFamily M V) (hAU : A ≤ U)
    (hc : subgroupCorank V A = 2)
    (hLC : L ≤ layerKernel (centralizer (A : Set G)))
    (hf : generalizedFitting (centralizer (U : Set G)) =
      pCore 2 (centralizer (U : Set G)))
    (d : E67Decomposition (sylowCentralizer (T : Subgroup G) V) M V A
      (layerEnvelope (centralizer (A : Set G)) (sylowCentralizer (T : Subgroup G) V))) :
    ∃ i : FixedFactors d U, L = d.block i.val := by
  let _ := h.elementary
  let H := centralizer (U : Set G)
  let Q := sylowCentralizer (T : Subgroup G) V
  let R := layerEnvelope (centralizer (A : Set G)) Q
  let B : FixedFactors d U → Subgroup H := fun i => (d.block i.val).subgroupOf H
  have hVH : V ≤ H := V.le_centralizer.trans (Subgroup.centralizer_le hU.1)
  have hHA : H ≤ centralizer (A : Set G) := Subgroup.centralizer_le hAU
  have hQA : Q ≤ centralizer (A : Set G) :=
    (Chapter1.isSylowIn_iff.mp (h.sylow_obstruction hA)).2.1
  have hB (i : FixedFactors d U) : ChapterC.IsBlock (B i) := by
    have hbR : ChapterC.IsBlock ((d.block i.val).subgroupOf R) :=
      ⟨inferInstance, (d.type i.val).chi.short.of_mulEquiv
        (subgroupOfEquivOfLe (d.le i.val)).symm, d.subnormal i.val⟩
    have hbA := block_lift_from_layerEnvelope hQA
      (T.isPGroup'.to_le inf_le_left) (d.le i.val) hbR
    exact ⟨inferInstance, (d.type i.val).chi.short.of_mulEquiv
      (subgroupOfEquivOfLe i.property).symm, hbA.subnormal.comap (inclusion hHA)⟩
  have hmap : (⨆ i, B i).map H.subtype = fixedFactorJoin d U := by
    rw [Subgroup.map_iSup]
    exact iSup_congr fun i => map_subgroupOf_eq_of_le i.property
  obtain ⟨S, hS⟩ := h.sylow_obstruction hU
  have hVS : V.subgroupOf H ≤ centralizer (S : Set H) := by
    intro v hv
    apply mem_centralizer_iff.mpr
    intro s hs
    have hsQ : (s : G) ∈ Q := by
      change (s : G) ∈ sylowCentralizer (T : Subgroup G) V
      rw [← hS]
      exact mem_map_of_mem H.subtype hs
    apply Subtype.ext
    exact (mem_centralizer_iff.mp hsQ.2 v hv).symm
  have hcover : ∀ l ∈ L.subgroupOf H,
      ∃ m ∈ centralizer (V.subgroupOf H : Set H), ∃ b ∈ ⨆ i, B i, m * b = l := by
    intro l hl
    have hlR : (l : G) ∈ R := (hLC.trans le_sup_left) hl
    have hp : (l : G) ∈ ((R ⊓ centralizer (V : Set G) : Subgroup G) : Set G) *
        (fixedFactorJoin d U : Set G) := by
      rw [← hprod U hU hUh A hA hAU hc d]
      exact ⟨hlR, l.property⟩
    obtain ⟨m, hm, b, hb, heq⟩ := hp
    have hmH : m ∈ H := Subgroup.centralizer_le hU.1 hm.2
    obtain ⟨bH, hbH, heB⟩ := mem_map.mp (hmap.symm ▸ hb)
    refine ⟨⟨m, hmH⟩, ?_, bH, hbH, ?_⟩
    · apply mem_centralizer_iff.mpr
      intro v hv
      exact Subtype.ext (mem_centralizer_iff.mp hm.2 v hv)
    · apply Subtype.ext
      change m * (bH : G) = (l : G)
      change (bH : G) = b at heB
      rw [heB]
      exact heq
  have hescape : ¬ L.subgroupOf H ≤ centralizer (V.subgroupOf H : Set H) := by
    intro hz
    apply he
    apply le_trans _ h.centralizer_le
    intro l hl
    apply mem_centralizer_iff.mpr
    intro v hv
    have hh := mem_centralizer_iff.mp (hz (show (⟨l, hL.1 hl⟩ : H) ∈ L.subgroupOf H from hl))
      (⟨v, hVH hv⟩ : H) hv
    exact congrArg Subtype.val hh
  obtain ⟨i, hi⟩ := block_eq_factor_of_centralizing_product hf S
    (L.subgroupOf H) (V.subgroupOf H) hL.2.1 hVS B hB
    (h19 H (fun _ => c19Condition_centralizer h21 hU.1 hU.2.1)) hcover hescape
  refine ⟨i, ?_⟩
  have hm := congrArg (Subgroup.map H.subtype) hi
  change (L.subgroupOf H).map H.subtype = ((d.block i.val).subgroupOf H).map H.subtype at hm
  rw [map_subgroupOf_eq_of_le (show L ≤ H from hL.1),
    map_subgroupOf_eq_of_le (show d.block i.val ≤ H from i.property)] at hm
  exact hm

/-- Assembly from the centralizer product and the permitted earlier-source facts. -/
theorem envelopeBlockDetection_of_centralizerProduct
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (h67 : E67Input T M V) (h19 : BlockCommutationInput G) (h21 : OddCoreFree V)
    (hchar : ∀ U : Subgroup G, IsHyperplane V U →
      generalizedFitting (centralizer (U : Set G)) = pCore 2 (centralizer (U : Set G)))
    (hprod : EnvelopeCentralizerProduct T M V) :
    EnvelopeBlockDetection (sylowCentralizer (T : Subgroup G) V) M V := by
  intro U hU hUh L hL _ he A hA hAU hc hLC
  obtain ⟨hRA, _, hf⟩ := three_envelope_setup h h21 hA
  have hR : HasCharacteristicTwo
      (layerEnvelope (centralizer (A : Set G)) (sylowCentralizer (T : Subgroup G) V)) := by
    have hh := ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
      (G := layerEnvelope (centralizer (A : Set G)) (sylowCentralizer (T : Subgroup G) V))
    rw [hf] at hh
    exact hh
  obtain ⟨d⟩ := h67 A hA _ le_sup_right hRA hR
  obtain ⟨i, hi⟩ := envelope_factor_of_centralizerProduct h h19 h21 hprod
    hU hUh hL he hA hAU hc hLC (hchar U hUh) d
  exact ⟨d.block i.val, hi.le, d.le i.val,
    ⟨inferInstance, (d.type i.val).chi.short.of_mulEquiv
      (subgroupOfEquivOfLe (d.le i.val)).symm, d.subnormal i.val⟩, d.type i.val⟩

/-- Construction of the containing block from the permitted source inputs.
The set product is proved by the factor transporters, and the selected E.6.7
factor supplies both the literal chi-zero module and subnormality in the
envelope. Hypothesis E.6.15 is unnecessary once the stated earlier conclusions
are supplied. The layer-centralizing placement remains the local hypothesis
of `EnvelopeBlockDetection`. -/
theorem envelopeBlockDetection
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (h67 : E67Input T M V) (h19 : BlockCommutationInput G) (h21 : OddCoreFree V)
    (hchar : ∀ U : Subgroup G, IsHyperplane V U →
      generalizedFitting (centralizer (U : Set G)) = pCore 2 (centralizer (U : Set G))) :
    EnvelopeBlockDetection (sylowCentralizer (T : Subgroup G) V) M V :=
  envelopeBlockDetection_of_centralizerProduct h h67 h19 h21 hchar
    (envelopeCentralizerProduct h h21)

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three
