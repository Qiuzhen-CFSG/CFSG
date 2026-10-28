module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Block.Inputs
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.TerminalReduction
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.Representation.BinaryPermutation.FiveAction
public import Theory.Representation.BinaryPermutationMulAction
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

/-!
# The intrinsic A₅ block after terminal core collapse

Under the terminal tilde commutator equality and S=V_L, G.2.4(2) gives
I=L. Hence the actual intrinsic two-core of L is V_L. The earlier star
kernel identifies L/O₂(L) with the given starred A₅ through the restriction
of LT→LT/O₂(LT).

Irreducibility and the nonzero seed commutator give [V_L,L]=V_L and
C_{V_L}(L)=1. Faithfulness of the given five-point core makes O₂(L)
self-centralizing, so F*(L)=O₂(L). These facts establish every clause of
IsShort. The block module isomorphism then uses its literal central
quotient and transports the supplied orthogonal core through
coreEquivNatural, with the original conjugation action intertwined.

The core-collapse premise is explicit: its producer is the terminal
collapse branch, and the final G.2.4(8) assembly must discharge it. The
local-core containment O₂(L₁)≤Q_H is not needed again after this collapse.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.4(8), printed pp.334–335; definitions C.1.7 and C.1.12.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive
open Setup Block ChapterC
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}
namespace Hypothesis
variable (d : Hypothesis D g) (c : EarlierStructure D g)
    (hfull : ⁅D.tilde D.U, D.tilde D.L₁⁆ = D.tilde D.U)
    (hS : D.S g = D.VL)
include d c hfull hS

/-- The collapsed source core, embedded in the original ambient group. -/
theorem intrinsic_core_image : D.L.pCoreIn 2 = D.VL := by
  have he := d.terminal_group_eq hfull c.generated
  simpa only [Setup.S, he] using hS

/-- After I=L the orthogonal layer lies in L itself. -/
theorem intrinsic_VL_le_L : D.VL ≤ D.L := by
  rw [← d.intrinsic_core_image c hfull hS]
  exact pCoreIn_le 2 D.L

/-- The intrinsic two-core is the restriction of the original orthogonal layer. -/
theorem intrinsic_core : pCore 2 D.L = D.VL.subgroupOf D.L := by
  apply map_injective D.L.subtype_injective
  rw [map_subgroupOf_eq_of_le (d.intrinsic_VL_le_L c hfull hS)]
  exact d.intrinsic_core_image c hfull hS

/-- The restricted LT-quotient map has exactly the intrinsic two-core as kernel. -/
theorem intrinsic_star_kernel : (starProjection D).ker = pCore 2 D.L := by
  have hker : D.L.pCoreIn 2 = D.L ⊓ D.LT.pCoreIn 2 := by
    rw [d.intrinsic_core_image c hfull hS, ← hS, c.star_kernel,
      d.terminal_group_eq hfull c.generated]
  ext a
  have hiff : a ∈ (starProjection D).ker ↔ (a : G) ∈ D.LT.pCoreIn 2 := by
    change starProjection D a = 1 ↔ _
    rw [Subtype.ext_iff]
    change (QuotientGroup.mk (inclusion (show D.L ≤ D.LT from le_sup_left) a) : D.Star) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro ha
      exact ⟨_, ha, rfl⟩
    · rintro ⟨b, hb, he⟩
      exact (show b = inclusion (show D.L ≤ D.LT from le_sup_left) a from Subtype.ext he) ▸ hb
  rw [hiff]
  constructor
  · intro ha
    have haS : (a : G) ∈ D.L.pCoreIn 2 := hker.symm ▸ ⟨a.property, ha⟩
    obtain ⟨b, hb, he⟩ := haS
    exact (show b = a from Subtype.ext he) ▸ hb
  · intro ha
    exact (hker ▸ (show (a : G) ∈ D.L.pCoreIn 2 from ⟨a, ha, rfl⟩)).2

/-- The actual star projection induces the quotient identification with A₅. -/
noncomputable def intrinsic_quotientIso : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 5) :=
  ((QuotientGroup.quotientMulEquivOfEq (d.intrinsic_star_kernel c hfull hS).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (starProjection D)
      (starProjection_surjective D))).trans d.model

/-- The quotient identification retains the original star map on representatives. -/
theorem intrinsic_quotientIso_mk (l : D.L) :
    d.intrinsic_quotientIso c hfull hS (QuotientGroup.mk' (pCore 2 D.L) l) =
      d.model (starProjection D l) := rfl

omit c hfull hS in
/-- The nonzero seed commutator and irreducibility give full commutator generation. -/
theorem intrinsic_commutator : ⁅D.VL, D.L⁆ = D.VL := by
  have hle := le_normalizer_iff_commutator_le_left.mp (L_normalizes_VL D)
  rcases d.irreducible ⁅D.VL, D.L⁆ hle (normalizer_commutator_ge_right _ _) with he | he
  · have hv : D.V ≤ ⁅D.VL, D.L⁆ := by
      rw [d.seed_eq]
      exact commutator_mono le_rfl ((map_subtype_le _).trans inf_le_left)
    have hp : D.V₁ ≤ (⊥ : Subgroup G) := by
      rw [← he]
      exact d.setup.point_le.trans hv
    exact (d.setup.point_ne_bot (bot_unique hp)).elim
  · exact he

/-- The defining block commutator maps onto the original orthogonal layer. -/
theorem intrinsic_blockU_image : (blockU D.L).map D.L.subtype = D.VL := by
  rw [blockU, map_commutator]
  change ⁅D.L.pCoreIn 2, (⊤ : Subgroup D.L).map D.L.subtype⁆ = _
  rw [← MonoidHom.range_eq_map, range_subtype, d.intrinsic_core_image c hfull hS]
  exact d.intrinsic_commutator

/-- The defining block commutator is the entire intrinsic two-core. -/
theorem intrinsic_blockU : blockU D.L = pCore 2 D.L := by
  apply map_injective D.L.subtype_injective
  exact (d.intrinsic_blockU_image c hfull hS).trans
    (d.intrinsic_core_image c hfull hS).symm

omit [Finite G] d c hfull hS in
private theorem intrinsic_normalizer_map (N : Subgroup D.L) (hn : N.Normal) :
    D.L ≤ normalizer (N.map D.L.subtype : Set G) := by
  intro l hl
  rw [mem_normalizer_iff]
  intro n
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact mem_map_of_mem _ (hn.conj_mem x hx ⟨l, hl⟩)
  · intro hx
    obtain ⟨x, hx, he⟩ := hx
    have hc := mem_map_of_mem D.L.subtype (hn.conj_mem x hx (⟨l, hl⟩ : D.L)⁻¹)
    change l⁻¹ * (x : G) * (l⁻¹)⁻¹ ∈ N.map D.L.subtype at hc
    change (x : G) = l * n * l⁻¹ at he
    rw [he, inv_inv] at hc
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right, inv_mul_cancel, mul_one] using hc

/-- Every L-normal subgroup of the block layer is trivial or the whole layer. -/
theorem intrinsic_invariant_core (N : Subgroup D.L) (hn : N.Normal)
    (hN : N ≤ blockU D.L) : N = ⊥ ∨ N = blockU D.L := by
  have hm : N.map D.L.subtype ≤ D.VL := by
    rw [← d.intrinsic_blockU_image c hfull hS]
    exact map_mono hN
  rcases d.irreducible _ hm (intrinsic_normalizer_map N hn) with he | he
  · left
    apply map_injective D.L.subtype_injective
    simpa only [Subgroup.map_bot] using he
  · right
    apply map_injective D.L.subtype_injective
    exact he.trans (d.intrinsic_blockU_image c hfull hS).symm

/-- The source point survives in the block commutator layer. -/
theorem intrinsic_blockU_ne_bot : blockU D.L ≠ ⊥ := by
  intro he
  have hm := d.intrinsic_blockU_image c hfull hS
  rw [he, Subgroup.map_bot] at hm
  exact d.setup.point_ne_bot (bot_unique
    ((le_conjugateSpanBy D.V₁ D.L).trans hm.ge))

/-- The orthogonal block layer has no nonidentity central elements of L. -/
theorem intrinsic_fixed_eq_bot : blockU D.L ⊓ center D.L = ⊥ := by
  rcases d.intrinsic_invariant_core c hfull hS (blockU D.L ⊓ center D.L)
    inferInstance inf_le_left with he | he
  · exact he
  · have hc : pCore 2 D.L ≤ center D.L := by
      rw [← d.intrinsic_blockU c hfull hS, ← he]
      exact inf_le_right
    have hb : blockU D.L = ⊥ := commutator_top_right_eq_bot_iff_le_center.mpr hc
    exact (d.intrinsic_blockU_ne_bot c hfull hS hb).elim

/-- The literal invariant-subgroup interval satisfies the short-group condition. -/
theorem intrinsic_irreducible : BlockModuleIrreducible D.L := by
  refine ⟨?_, fun N hn _ hN => ?_⟩
  · rw [d.intrinsic_fixed_eq_bot c hfull hS]
    exact bot_lt_iff_ne_bot.mpr (d.intrinsic_blockU_ne_bot c hfull hS)
  · rw [d.intrinsic_fixed_eq_bot c hfull hS]
    exact d.intrinsic_invariant_core c hfull hS N hn hN

/-- The actual denominator in the block module quotient is trivial. -/
theorem intrinsic_blockFixed : blockFixed D.L = ⊥ := by
  apply bot_unique
  intro v hv
  apply Subtype.ext
  have hh : (v : D.L) ∈ blockU D.L ⊓ center D.L := ⟨v.property, hv⟩
  rwa [d.intrinsic_fixed_eq_bot c hfull hS, mem_bot] at hh

/-- Faithfulness of the five-point core makes the intrinsic two-core self-centralizing. -/
theorem intrinsic_selfCentralizing :
    centralizer (pCore 2 D.L : Set D.L) ≤ pCore 2 D.L := by
  intro l hl
  have hfix (v : D.VL) :
      BinaryPermutation.coreRepresentation (Fin 5) (d.model (starProjection D l)).val
        (d.coordinates v).toAdd = (d.coordinates v).toAdd := by
    let vL : D.L := ⟨v, d.intrinsic_VL_le_L c hfull hS v.property⟩
    have hvL : vL ∈ pCore 2 D.L := by
      rw [d.intrinsic_core c hfull hS]
      exact v.property
    have hc := congrArg Subtype.val (hl vL hvL)
    change (v : G) * (l : G) = (l : G) * (v : G) at hc
    have he : (l : G) * (v : G) * (l : G)⁻¹ = v := by
      rw [← hc, mul_inv_cancel_right]
    have heq := d.equivariant l v
    have hsub : (⟨(l : G) * (v : G) * (l : G)⁻¹,
      (mem_normalizer_iff.mp (L_normalizes_VL D l.property) v).mp v.property⟩ : D.VL) = v :=
      Subtype.ext he
    rw [hsub] at heq
    exact (congrArg Multiplicative.toAdd heq).symm
  have hperm : (d.model (starProjection D l)).val = 1 := by
    apply BinaryPermutation.FiveGeometry.eq_one_of_fixes_hyperplane
    intro v _
    obtain ⟨w, hw⟩ := d.coordinates.surjective (Multiplicative.ofAdd v)
    simpa only [hw, toAdd_ofAdd] using hfix w
  have hmodel : d.model (starProjection D l) = 1 := Subtype.ext hperm
  rw [← d.intrinsic_star_kernel c hfull hS]
  exact d.model.injective (hmodel.trans d.model.map_one.symm)

/-- The supplied orthogonal coordinates make the intrinsic two-core elementary abelian. -/
theorem intrinsic_elementary_core : IsElementaryAbelian 2 (pCore 2 D.L) := by
  let := d.VL_elementary
  rw [d.intrinsic_core c hfull hS]
  exact IsElementaryAbelian.subgroupOf (d.intrinsic_VL_le_L c hfull hS)

/-- All five source structural conditions, including the quasisimple quotient, hold in L. -/
theorem intrinsic_short : IsShort D.L := by
  let : IsElementaryAbelian 2 (pCore 2 D.L) := d.intrinsic_elementary_core c hfull hS
  let : IsQuasisimple (alternatingGroup (Fin 5)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  refine {
    finite := inferInstance
    twoPerfect := (pResidual_eq_top_iff 2 D.L).mp d.setup.residual
    fitting := generalizedFitting_eq_pCore_of_selfCentralizing 2
      (d.intrinsic_selfCentralizing c hfull hS)
    elementary := ?_
    central := ?_
    quotient := Or.inl (IsQuasisimple.of_mulEquiv (d.intrinsic_quotientIso c hfull hS).symm)
    irreducible := d.intrinsic_irreducible c hfull hS }
  · rw [d.intrinsic_blockU c hfull hS]
    infer_instance
  · rw [d.intrinsic_blockU c hfull hS]
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm (⟨y,hy⟩ : pCore 2 D.L) ⟨x,hx⟩)

/-- The intrinsic block layer is identified with V_L through ambient inclusion. -/
noncomputable def intrinsic_layerIso : blockU D.L ≃* D.VL :=
  ((blockU D.L).equivMapOfInjective D.L.subtype D.L.subtype_injective).trans
    (MulEquiv.subgroupCongr (d.intrinsic_blockU_image c hfull hS))

/-- The layer identification preserves the original ambient element. -/
theorem intrinsic_layerIso_coe (u : blockU D.L) :
    (d.intrinsic_layerIso c hfull hS u : G) = (u : D.L) := rfl

/-- The literal block module quotient is the natural binary five-point module. -/
noncomputable def intrinsic_moduleIso : BlockModule D.L ≃*
    Multiplicative (BinaryPermutation.natural (Fin 5)) :=
  (((QuotientGroup.quotientMulEquivOfEq (d.intrinsic_blockFixed c hfull hS)).trans
    QuotientGroup.quotientBot).trans (d.intrinsic_layerIso c hfull hS)).trans
      (d.coordinates.trans
        (BinaryPermutation.coreEquivNatural (Fin 5) (by decide)).toAddEquiv.toMultiplicative)

/-- On representatives the module identification is the supplied core coordinate map
followed by coreEquivNatural. -/
theorem intrinsic_moduleIso_mk (u : blockU D.L) :
    d.intrinsic_moduleIso c hfull hS (QuotientGroup.mk' (blockFixed D.L) u) =
      Multiplicative.ofAdd (BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
        (d.coordinates (d.intrinsic_layerIso c hfull hS u)).toAdd) := rfl

/-- The original conjugation and quotient maps intertwine with the natural A₅ action. -/
noncomputable def intrinsic_blockModel : BlockModuleModel D.L
    ((BinaryPermutation.naturalMulAction (Fin 5)).comp (alternatingGroup (Fin 5)).subtype) where
  quotientIso := d.intrinsic_quotientIso c hfull hS
  moduleIso := d.intrinsic_moduleIso c hfull hS
  intertwining l u := by
    rw [d.intrinsic_quotientIso_mk c hfull hS,
      d.intrinsic_moduleIso_mk c hfull hS, d.intrinsic_moduleIso_mk c hfull hS]
    let v := d.intrinsic_layerIso c hfull hS u
    have hlayer : d.intrinsic_layerIso c hfull hS (blockConjugate D.L l u) =
        ⟨(l : G) * (v : G) * (l : G)⁻¹,
          (mem_normalizer_iff.mp (L_normalizes_VL D l.property) v).mp v.property⟩ := by
      apply Subtype.ext
      rfl
    rw [hlayer, d.equivariant]
    exact congrArg Multiplicative.ofAdd
      (BinaryPermutation.coreEquivNatural_equivariant (Fin 5) (by decide)
        (d.model (starProjection D l)).val (d.coordinates v).toAdd)

/-- The intrinsic A₅-block conclusion of G.2.4(8), conditional only on the supplied
earlier structure, terminal commutator equality and core collapse. -/
theorem intrinsic_alternatingBlock : IsAlternatingBlock D.L 5 := by
  refine ⟨by decide, d.intrinsic_short c hfull hS,
    (BinaryPermutation.naturalMulAction (Fin 5)).comp (alternatingGroup (Fin 5)).subtype,
    ⟨d.intrinsic_blockModel c hfull hS⟩, ?_⟩
  intro a v
  rfl

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.AlternatingFive
