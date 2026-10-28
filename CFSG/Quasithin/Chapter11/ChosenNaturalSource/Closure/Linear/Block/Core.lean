module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Collapse
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# The original SL₃ block after the three-conjugate collapse

The equality S=S₂ makes S elementary and gives [S,L]=V. Relative normality
places O₂(L) in S, so its commutator layer is exactly the original chosen V.
The marked natural action proves that V has no fixed part and that O₂(L)
is self-centralizing. These facts establish every short-group clause.

The block model retains the original star projection, its kernel O₂(L),
and the actual conjugation coordinates. In particular this is an SL₃
block, with the full special-linear quotient and its center retained.
Only the permitted marked G.2 hypothesis, U≤T, Φ(U)≤V₁ and S=S₂ are
inputs. The central splitting and exceptional overgroup reduction are
separate steps; this module does not assert O₂(L)=V.

Source: Aschbacher--Smith, 11.5.7, printed p.782, and C.1.7, C.1.30.
-/

@[expose] public noncomputable section
open Subgroup Matrix
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterG.Section02.LinearThree
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D) {x y : G}
  (d : Hypothesis (setup E) E.input.field.Carrier E.input.field.degree x y)

include d

theorem componentCore_le_threeCore
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁) :
    L.pCoreIn 2 ≤ threeCore E x y := by
  apply pCoreIn_mono_of_normalizes (d.L_le_I hUT hf)
  exact (d.I_le_LT hUT).trans
    (sup_le L.le_normalizer D.sylow_normalizes_component)

theorem threeCore_elementary
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y) :
    IsElementaryAbelian 2 (threeCore E x y) := by
  rw [hc]
  exact (d.intersection hUT hf).2.2.2.2

theorem threeCore_commutator
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y) :
    ⁅threeCore E x y,L⁆ = V := by
  apply le_antisymm
  · rw [hc]
    exact (commutator_mono le_rfl (d.L_le_I hUT hf)).trans
      (d.intersection hUT hf).2.2.2.1
  · exact D.eq_commutator.le.trans
      (commutator_mono ((d.central_first_of_source hUT hf).trans inf_le_left) le_rfl)

theorem componentCore_commutator
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y) :
    ⁅L.pCoreIn 2,L⁆ = V := by
  apply le_antisymm
  · exact (commutator_mono (componentCore_le_threeCore E d hUT hf) le_rfl).trans
      (threeCore_commutator E d hUT hf hc).le
  · exact D.eq_commutator.le.trans (commutator_mono D.le_componentCore le_rfl)

theorem blockU_map
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y) :
    (ChapterC.blockU L).map L.subtype = V := by
  rw [ChapterC.blockU, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
  exact componentCore_commutator E d hUT hf hc

theorem chosen_fixed_eq_bot : V ⊓ centralizer (L : Set G) = ⊥ := by
  have hn : L ≤ normalizer ((V ⊓ centralizer (L : Set G) : Subgroup G) : Set G) :=
    (le_inf D.normalizes
      (L.le_normalizer.trans (normalizer_le_normalizer_centralizer L))).trans
      inf_normalizer_le_normalizer_inf
  rcases d.irreducible _ inf_le_left hn with h | h
  · exact h
  · have hz : V ≤ centralizer (L : Set G) := h.ge.trans inf_le_right
    exact (D.ne_bot (D.eq_commutator.trans
      (commutator_eq_bot_iff_le_centralizer.mpr hz))).elim


omit d in
set_option backward.isDefEq.respectTransparency false in
theorem starProjection_ker : (starProjection (setup E)).ker = pCore 2 L := by
  have hcore : L.pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left
      (sup_le L.le_normalizer D.sylow_normalizes_component)
  ext l
  rw [MonoidHom.mem_ker]
  change (⟨_, _⟩ : (setup E).star L) = 1 ↔ _
  rw [Subtype.ext_iff]
  change QuotientGroup.mk' (pCore 2 ↥(L ⊔ (T : Subgroup G)))
    (inclusion (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left) l) = 1 ↔ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    have hl := inf_pCoreIn_le_of_le 2 (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
      ⟨l.property, mem_map_of_mem _ h⟩
    obtain ⟨a, ha, he⟩ := hl
    exact (Subtype.ext he : a = l) ▸ ha
  · intro h
    obtain ⟨a, ha, he⟩ := hcore (mem_map_of_mem L.subtype h)
    exact (Subtype.ext he : a = inclusion le_sup_left l) ▸ ha

noncomputable def componentQuotientEquiv :
    (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) E.input.field.Carrier :=
  let f : L →* (setup E).star L := starProjection (setup E)
  letI : f.ker.Normal := inferInstance
  ((QuotientGroup.quotientMulEquivOfEq (show pCore 2 L = f.ker from
      (starProjection_ker E).symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective f
      (starProjection_surjective (setup E)))).trans d.model

theorem componentQuotientEquiv_mk (l : L) :
    componentQuotientEquiv E d (QuotientGroup.mk' (pCore 2 L) l) =
      d.model (starProjection (setup E) l) := rfl

noncomputable def blockEquiv
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y) : ChapterC.blockU L ≃* V :=
  ((ChapterC.blockU L).equivMapOfInjective L.subtype L.subtype_injective).trans
    (MulEquiv.subgroupCongr (blockU_map E d hUT hf hc))

theorem blockEquiv_val
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y) (v : ChapterC.blockU L) :
    (blockEquiv E d hUT hf hc v : G) = (v.val : G) := rfl

theorem blockFixed_eq_bot
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y) : ChapterC.blockFixed L = ⊥ := by
  apply eq_bot_iff.mpr
  intro v hv
  have hz : (v.val : G) ∈ centralizer (L : Set G) := by
    intro l hl
    exact congrArg Subtype.val ((mem_center_iff.mp hv) ⟨l, hl⟩)
  have hvV : (v.val : G) ∈ V :=
    (blockU_map E d hUT hf hc).le (mem_map_of_mem _ v.property)
  have he : (v.val : G) = 1 := mem_bot.mp ((chosen_fixed_eq_bot E d).le ⟨hvV, hz⟩)
  exact mem_bot.mpr (Subtype.ext (Subtype.ext he))

noncomputable def blockModuleEquiv
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y) :
    ChapterC.BlockModule L ≃* Multiplicative (Fin 3 → E.input.field.Carrier) :=
  (((QuotientGroup.quotientMulEquivOfEq (blockFixed_eq_bot E d hUT hf hc)).trans
    QuotientGroup.quotientBot).trans (blockEquiv E d hUT hf hc)).trans d.coordinates


theorem component_fitting : Theory.GroupTheory.generalizedFitting L = pCore 2 L := by
  apply Theory.GroupTheory.generalizedFitting_eq_pCore_of_selfCentralizing 2
  intro l hl
  have he : d.model (starProjection (setup E) l) = 1 := by
    apply Matrix.SpecialLinearGroup.toLin'_injective
    rw [map_one]
    ext w : 1
    obtain ⟨v, rfl⟩ := d.coordinates.surjective (Multiplicative.ofAdd w)
    change (d.model (starProjection (setup E) l)).val *ᵥ (d.coordinates v).toAdd =
      (d.coordinates v).toAdd
    rw [← d.equivariant l v]
    congr 2
    apply Subtype.ext
    have hv : (⟨v, D.le_component v.property⟩ : L) ∈ pCore 2 L := by
      obtain ⟨a, ha, he⟩ := D.le_componentCore v.property
      exact (Subtype.ext he : a = ⟨v, D.le_component v.property⟩) ▸ ha
    have hh := congrArg Subtype.val (hl _ hv)
    change (v : G) * (l : G) = (l : G) * (v : G) at hh
    change (l : G) * (v : G) * (l : G)⁻¹ = (v : G)
    rw [← hh, mul_inv_cancel_right]
  have hk : l ∈ (starProjection (setup E)).ker :=
    MonoidHom.mem_ker.mpr (d.model.injective (he.trans d.model.map_one.symm))
  rwa [starProjection_ker E] at hk

theorem component_short
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y) : ChapterC.IsShort L := by
  have hmap := blockU_map E d hUT hf hc
  have hcent : ChapterC.blockU L ⊓ center L = ⊥ := by
    rw [← ChapterC.blockFixed_map, blockFixed_eq_bot E d hUT hf hc, Subgroup.map_bot]
  have hne : ChapterC.blockU L ≠ ⊥ := by
    intro he
    rw [he, Subgroup.map_bot] at hmap
    exact D.ne_bot hmap.symm
  refine ⟨inferInstance, (pResidual_eq_top_iff 2 L).mp d.setup.residual,
    component_fitting E d, ?_, ?_, Or.inl E.input.source.quasisimple, ?_⟩
  · let := D.elementary
    exact IsElementaryAbelian.of_surjective (blockEquiv E d hUT hf hc).symm.toMonoidHom
      (blockEquiv E d hUT hf hc).symm.surjective
  · intro v hv w hw
    have hvV : (v : G) ∈ V := hmap.le (mem_map_of_mem L.subtype hv)
    have hcore : L.pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
      pCoreIn_mono_of_normalizes le_sup_left
        (sup_le L.le_normalizer D.sylow_normalizes_component)
    exact Subtype.ext ((D.core_centralizes (hcore (mem_map_of_mem L.subtype hw)) _ hvV).symm)
  · refine ⟨by rw [hcent]; exact bot_lt_iff_ne_bot.mpr hne, ?_⟩
    intro N hN _ hNU
    let := hN
    have hn : L ≤ normalizer (N.map L.subtype : Set G) := by
      calc
        L = (normalizer (N : Set L)).map L.subtype := by
          rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
        _ ≤ _ := N.le_normalizer_map L.subtype
    rcases d.irreducible (N.map L.subtype) ((map_mono hNU).trans_eq hmap) hn with h | h
    · left
      rw [hcent]
      exact map_injective L.subtype_injective (h.trans (Subgroup.map_bot L.subtype).symm)
    · right
      exact map_injective L.subtype_injective (h.trans hmap.symm)

def naturalAction : Matrix.SpecialLinearGroup (Fin 3) E.input.field.Carrier →*
    MulAut (Multiplicative (Fin 3 → E.input.field.Carrier)) where
  toFun g := (Matrix.SpecialLinearGroup.toLin' g).toAddEquiv.toMultiplicative
  map_one' := by
    ext v : 1
    change Matrix.SpecialLinearGroup.toLin' 1 (Multiplicative.toAdd v) = Multiplicative.toAdd v
    rw [map_one]
    rfl
  map_mul' g h := by
    ext v : 1
    change Matrix.SpecialLinearGroup.toLin' (g * h) (Multiplicative.toAdd v) =
      Matrix.SpecialLinearGroup.toLin' g (Matrix.SpecialLinearGroup.toLin' h (Multiplicative.toAdd v))
    rw [map_mul]
    rfl

noncomputable def blockModel
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y) : ChapterC.BlockModuleModel L (naturalAction E) where
  quotientIso := componentQuotientEquiv E d
  moduleIso := blockModuleEquiv E d hUT hf hc
  intertwining l v := by
    change d.coordinates (blockEquiv E d hUT hf hc (ChapterC.blockConjugate L l v)) =
      naturalAction E (d.model (starProjection (setup E) l))
        (d.coordinates (blockEquiv E d hUT hf hc v))
    exact d.equivariant l (blockEquiv E d hUT hf hc v)

theorem component_sl3_block
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y) :
    ChapterC.IsSL3EvenBlock L E.input.field.degree :=
  ⟨Nat.succ_le_of_lt d.exponent_pos, component_short E d hUT hf hc,
    E.input.field.Carrier, inferInstance, inferInstance, d.field_card,
    naturalAction E, ⟨blockModel E d hUT hf hc⟩, fun _ _ => rfl⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block
