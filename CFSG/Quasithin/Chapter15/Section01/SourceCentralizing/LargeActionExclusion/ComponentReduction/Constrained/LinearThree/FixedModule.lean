module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.LinearThree.ResidualAction
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction
public import Theory.GroupAction.FixedIndexTwoResidual

/-!
# The exchanged residual fixes the binary SL₃ core quotient

If V₂ lies in U(L), its image in U(L)/C_U(L) has order four in a
module of order eight. A two-perfect actor fixing this index-two subgroup
fixes the entire module. The actual natural-module intertwining equation
then makes it fix L/O₂(L). The complementary branch uses the quotient
involution fixed by that same actor, whose automorphism fixer is a two-group.
Together these prove trivial quotient action without assuming either plane
row or replacing SL₃(2) by a rank-two residual model.

Source: Aschbacher--Smith 15.1.24(2), printed p.1101. Lifting this quotient
centralization to L and the final normalizer contradiction remain with the
constrained-recognition owner.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}


private theorem quotient_fixed_of_module_fixed {L F : Type*} [Group L] [Field F]
    {ρ : Matrix.SpecialLinearGroup (Fin 3) F →* MulAut (Multiplicative (Fin 3 → F))}
    (m : BlockModuleModel L ρ)
    (hρ : ∀ g v, (ρ g v).toAdd = specialLinearNatural 3 g v.toAdd)
    (a : MulAut L) (ha : blockModuleAut a = 1) :
    quotientAut (pCore 2 L) a = 1 := by
  have hi : Function.Injective ρ := by
    intro g j he
    apply Matrix.SpecialLinearGroup.toLin'_injective
    apply LinearEquiv.ext
    intro v
    have hv := congrArg (fun k : MulAut (Multiplicative (Fin 3 → F)) =>
      (k (Multiplicative.ofAdd v)).toAdd) he
    simp only [hρ] at hv
    exact hv
  have hfix (u : blockU L) :
      QuotientGroup.mk' (blockFixed L) (MulAut.characteristic (blockU L) a u) =
        QuotientGroup.mk' (blockFixed L) u := by
    have hh := DFunLike.congr_fun ha (QuotientGroup.mk' (blockFixed L) u)
    rw [blockModuleAut_apply_mk] at hh
    exact hh
  apply MulEquiv.ext
  intro g
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) g
  rw [quotientAut_apply_mk]
  apply m.quotientIso.injective
  apply hi
  apply MulEquiv.ext
  intro v
  obtain ⟨u,rfl⟩ := m.moduleIso.surjective.comp
    (QuotientGroup.mk'_surjective (blockFixed L)) v
  dsimp only [Function.comp_apply]
  have he : MulAut.characteristic (blockU L) a (blockConjugate L l u) =
      blockConjugate L (a l) (MulAut.characteristic (blockU L) a u) := by
    apply Subtype.ext
    change a (l * (u : L) * l⁻¹) = a l * a (u : L) * (a l)⁻¹
    simp only [map_mul,map_inv]
  have hh := m.intertwining (a l) (MulAut.characteristic (blockU L) a u)
  rw [←he,hfix,hfix] at hh
  exact hh.symm.trans (m.intertwining l u)

/-- An order-four moving plane in the natural layer forces the exchanged
two-perfect residual to fix the natural module and then the core quotient. -/
theorem ExchangedSource.linearThree_exchanged_core_quotient_of_layer
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    {h : PreparedChosenModule T M V} (sp : d.PreExclusionSource h.normalized 3)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M) (a : d.ConstrainedL3Alternative)
    (hVU : d.nineMovingPlane ≤ d.linearThreeU)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    ⁅d.linearThreeY.map (MulAut.conj t).toMonoidHom,d.L⁆ ≤ d.L.pCoreIn 2 := by
  let A := d.linearThreeY.map (MulAut.conj t).toMonoidHom
  have hn : A ≤ normalizer (d.L : Set G) :=
    s.linearThree_exchanged_normalizes (h := h) sp hG hTM a ht htS
  obtain ⟨hp,hc,_⟩ := s.linearThree_exchanged_action (h := h) sp hTM a ht htS
  have hVL : d.nineMovingPlane ≤ d.L := hVU.trans (map_subtype_le _)
  have hEu : d.nineMovingPlane.subgroupOf d.L ≤ blockU d.L := by
    intro x hx
    obtain ⟨u,hu,he⟩ := hVU hx
    exact (Subtype.ext he : u = x) ▸ hu
  let i : d.nineMovingPlane →* blockU d.L := (inclusion hEu).comp
    (subgroupOfEquivOfLe hVL).symm.toMonoidHom
  let f := (QuotientGroup.mk' (blockFixed d.L)).comp i
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply le_bot_iff.mp
    intro x hx
    have hz0 : i x ∈ blockFixed d.L := (QuotientGroup.eq_one_iff _).mp hx
    have hz : (i x : d.L) ∈ center d.L := hz0
    have hxC : (x : G) ∈ centralizer (d.linearThreeY : Set G) := by
      intro y hy
      have hyL : y ∈ d.L := ((map_subtype_le _).trans inf_le_right) hy
      exact congrArg (fun z : d.L => (z : G)) (mem_center_iff.mp hz ⟨y,hyL⟩)
    exact Subtype.ext ((s.linearThree_moving_action_kernel (h := h) sp hTM a).2.2.le
      ⟨x.property,hxC⟩)
  have hcard : Nat.card f.range = 4 := by
    rw [←Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
    exact (s.linearThree_row_four_of_layer (h := h) sp hTM a hVU).2.2.2
  have hmodule : Nat.card (BlockModule d.L) = 8 := by simpa using a.block.module_card
  have hindex : f.range.index ≤ 2 := by
    have hh := f.range.card_mul_index
    rw [hcard,hmodule] at hh
    omega
  let b : A →* MulAut d.L := d.L.normalizerMonoidHom.comp (inclusion hn)
  let ρ := blockModuleAut.comp b
  let := a.block.2.1.module_elementary
  have hρ (y : A) : ρ y = 1 := MulAut.eq_one_of_pPerfect_of_fixed_index_le_two ρ hp
    (IsElementaryAbelian.isPGroup 2 (BlockModule d.L)) f.range hindex (by
      intro y x hx
      obtain ⟨v,rfl⟩ := hx
      change blockModuleAut (b y) (QuotientGroup.mk' (blockFixed d.L) (i v)) = _
      rw [blockModuleAut_apply_mk]
      have he : MulAut.characteristic (blockU d.L) (b y) (i v) = i v := by
        apply Subtype.ext
        apply Subtype.ext
        change (y : G) * (v : G) * (y : G)⁻¹ = v
        have hh := hc y.property v v.property
        rw [←hh,mul_inv_cancel_right]
      rw [he]
      rfl) y
  obtain ⟨F,_,_,_,ρF,⟨m⟩,hρF⟩ := a.block.2.2
  have hq (y : A) : quotientAut (pCore 2 d.L) (b y) = 1 :=
    quotient_fixed_of_module_fixed m hρF (b y) (hρ y)
  apply commutator_le.mpr
  intro y hy l hl
  have hh := DFunLike.congr_fun (hq ⟨y,hy⟩) (QuotientGroup.mk' (pCore 2 d.L) ⟨l,hl⟩)
  rw [quotientAut_apply_mk] at hh
  have hk : b ⟨y,hy⟩ ⟨l,hl⟩ * (⟨l,hl⟩ : d.L)⁻¹ ∈ pCore 2 d.L := by
    simpa only [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp hh
  exact mem_map.mpr ⟨_,hk,rfl⟩

/-- Both branches of the actual moving-plane calculation give trivial
action on L/O₂(L), with no rank-two assumption on that quotient. -/
theorem ExchangedSource.linearThree_exchanged_core_quotient
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    {h : PreparedChosenModule T M V} (sp : d.PreExclusionSource h.normalized 3)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M) (a : d.ConstrainedL3Alternative)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    ⁅d.linearThreeY.map (MulAut.conj t).toMonoidHom,d.L⁆ ≤ d.L.pCoreIn 2 := by
  rcases s.linearThree_layer_or_quotient_involution (h := h) sp hTM a with hU | ⟨v,hv,hv2⟩
  · exact s.linearThree_exchanged_core_quotient_of_layer (h := h) sp hG hTM a hU ht htS
  · exact s.linearThree_exchanged_core_quotient_of_involution (h := h) sp hG hTM a v hv hv2 ht htS

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
