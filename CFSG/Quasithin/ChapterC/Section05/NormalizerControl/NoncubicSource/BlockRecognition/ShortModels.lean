module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.BlockRecognition.ModuleRatio
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.AlternatingSevenMaximal.Basic
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven.Degree
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven.SixSpace
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTransfer
public import Theory.Representation.FactorDegreeFiltration.FiniteDual
public import Theory.Representation.Quotient
public import Theory.Representation.BinaryOffender.DualDisplacement
/-!
# Recognizing the two short A₇ block types

The intrinsic noncentral block representation is nontrivial and irreducible;
simplicity of its actual A₇ actor makes it faithful. Its dual cubic bound
therefore gives degree four or six by K.1.2. In degree six the point-stabilizer
recognition produces the actual permutation-module intertwiner. Degree four
is exactly the exceptional block definition. No module model is assumed.
Source: Aschbacher–Smith C.5.13, p.163; K.1.2, p.452.
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC
open ExceptionalRestrictions ChapterB.QuasisimpleSource
open Section05.NormalizerControl.EmbeddingSelection
universe u
variable {L : Type u} [Group L]
private theorem moduleRepresentation_ne_one (h : IsShort L) :
    letI := h.elementary
    letI := h.module_elementary
    moduleRepresentation h ≠ 1 := by
  let := h.elementary
  let := h.module_elementary
  let := h.module_nontrivial
  change moduleRepresentation h ≠ 1
  intro he
  have hk : Coinvariants.ker (uRepresentation h) ≤ (moduleProjection (L := L)).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,v⟩,rfl⟩
    change moduleProjection (uRepresentation h g v - v) = 0
    rw [map_sub,moduleProjection_equivariant,he]
    exact sub_self _
  rw [uRepresentation_moved h] at hk
  obtain ⟨w,hw⟩ := exists_ne (0 : Additive (BlockModule L))
  obtain ⟨v,rfl⟩ := moduleProjection_surjective w
  exact hw (hk Submodule.mem_top)

theorem short_a7_module_degree {κ : GroupClass.{u}} (h : IsShort L)
    (hs : IsSQTK κ (L ⧸ pCore 2 L))
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7)) :
    letI := h.elementary
    letI := h.module_elementary
    cubicRatio (moduleRepresentation h).dual ≤ 2 →
    Module.finrank (ZMod 2) (Additive (BlockModule L)) = 4 ∨
      Module.finrank (ZMod 2) (Additive (BlockModule L)) = 6 := by
  let := h.finite
  let := h.elementary
  let := h.module_elementary
  change cubicRatio (moduleRepresentation h).dual ≤ 2 → _
  intro hc
  let Q := L ⧸ pCore 2 L
  let σ := moduleRepresentation h
  let : IsSimpleGroup Q := AlternatingSevenMaximal.simple_of_model ⟨e⟩
  let : IsQuasisimple Q := h.quotient.resolve_right (by
    rw [AlternatingSevenMaximal.card_of_model ⟨e⟩]
    decide)
  have hf : Function.Injective σ := by
    rcases σ.normal_ker.eq_bot_or_eq_top with hz | ht
    · exact σ.ker_eq_bot_iff.mp hz
    · exact (moduleRepresentation_ne_one h (MonoidHom.ker_eq_top_iff.mp ht)).elim
  let : IsIrreducible σ := moduleRepresentation_irreducible h
  let : IsIrreducible σ.dual := Representation.isIrreducible_dual
  let et : (⊤ : Subgroup Q) ≃* alternatingGroup (Fin 7) := topEquiv.trans e
  have hi : ChapterK.Alternating.Input σ.dual κ (⊤ : Subgroup Q) := {
    sqtk := hs
    fitting := (generalizedFitting_eq_top_of_quasisimple (G := Q)).symm
    quasisimple := IsQuasisimple.of_mulEquiv topEquiv.symm
    faithful := faithful_dual σ hf
    irreducible := (irreducible_comp_surjective_iff (⊤ : Subgroup Q).subtype
      (fun a => ⟨⟨a,mem_top a⟩,rfl⟩) σ.dual).mpr inferInstance
    cubic_bound := hc
    quotient := Or.inr ⟨(QuotientGroup.quotientMulEquivOfEq
      (AlternatingSevenMaximal.center_of_model ⟨et⟩)).trans (QuotientGroup.quotientBot.trans et)⟩ }
  have hd := ChapterK.Alternating.sevenDegreeBound σ.dual κ ⊤ hi et
  simpa only [Subspace.dual_finrank_eq] using hd

theorem linearBlockModel_of_actionEquiv {H W : Type*} [Group H]
    [AddCommGroup W] [Module (ZMod 2) W]
    (h : IsShort L) (ρ : Representation (ZMod 2) H W) :
    letI := h.elementary
    letI := h.module_elementary
    ActionEquiv (moduleRepresentation h) ρ → IsLinearBlockModel L ρ := by
  let := h.elementary
  let := h.module_elementary
  change ActionEquiv (moduleRepresentation h) ρ → _
  intro E
  let r : H →* MulAut (Multiplicative W) := {
    toFun := fun g => (LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom g)).toAddEquiv.toMultiplicative
    map_one' := by ext w; exact congrArg Multiplicative.ofAdd (LinearMap.congr_fun ρ.map_one w.toAdd)
    map_mul' := fun g k => by ext w; exact congrArg Multiplicative.ofAdd (LinearMap.congr_fun (ρ.map_mul g k) w.toAdd) }
  refine ⟨r,⟨{
    quotientIso := E.groupEquiv
    moduleIso := E.linearEquiv.toAddEquiv.toMultiplicative
    intertwining := ?_ }⟩,fun g w => rfl⟩
  intro l u
  change Multiplicative.ofAdd (E.linearEquiv (Additive.ofMul (QuotientGroup.mk' (blockFixed L) (blockConjugate L l u)))) = _
  have he := E.intertwines (QuotientGroup.mk' (pCore 2 L) l)
    (Additive.ofMul (QuotientGroup.mk' (blockFixed L) u))
  have hp := congrArg Additive.ofMul (h.exists_quotient_moduleAction.choose_spec l u)
  exact congrArg Multiplicative.ofAdd ((congrArg E.linearEquiv hp.symm).trans he)

theorem short_a7_block_of_six (h : IsShort L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7)) :
    letI := h.elementary
    letI := h.module_elementary
    Module.finrank (ZMod 2) (Additive (BlockModule L)) = 6 → IsAlternatingBlock L 7 := by
  let := h.finite
  let := h.elementary
  let := h.module_elementary
  change Module.finrank (ZMod 2) (Additive (BlockModule L)) = 6 → _
  intro hd
  let ρ := moduleRepresentation h
  let τ := ρ.comp e.symm.toMonoidHom
  let : IsIrreducible τ := (irreducible_comp_surjective_iff e.symm.toMonoidHom
    e.symm.surjective ρ).mpr (moduleRepresentation_irreducible h)
  have hfixed := ChapterK.Alternating.SevenSixSpace.fixed_or_dual
    ChapterK.Alternating.SevenSixSpace.pointSimpleDegrees
    (τ.comp ChapterK.Alternating.SevenSixSpace.PointStabilizer.subtype) hd
  obtain ⟨a⟩ := ChapterK.Alternating.SevenSixSpace.of_point_fixed_or_dual τ hd hfixed
  refine ⟨by decide,h,linearBlockModel_of_actionEquiv h (alternatingNatural 7) ?_⟩
  refine ⟨e,a.toLinearEquiv,?_⟩
  intro g v
  have hh := LinearMap.congr_fun (a.toIntertwiningMap.isIntertwining' (e g)) v
  change a.toLinearEquiv (ρ (e.symm (e g)) v) = alternatingNatural 7 (e g) (a.toLinearEquiv v) at hh
  simpa only [e.symm_apply_apply] using hh

theorem short_a7_blocks_of_dual_cubic {κ : GroupClass.{u}} (h : IsShort L)
    (hs : IsSQTK κ (L ⧸ pCore 2 L))
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7)) :
    letI := h.elementary
    letI := h.module_elementary
    cubicRatio (moduleRepresentation h).dual ≤ 2 →
      IsAlternatingBlock L 7 ∨ IsExceptionalA7Block L := by
  let := h.finite
  let := h.elementary
  let := h.module_elementary
  change cubicRatio (moduleRepresentation h).dual ≤ 2 → _
  intro hc
  rcases short_a7_module_degree h hs e hc with hd | hd
  · right
    refine ⟨h,⟨e⟩,?_⟩
    calc
      Nat.card (BlockModule L) = Nat.card (Additive (BlockModule L)) := rfl
      _ = 2 ^ 4 := by rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hd]
  · exact Or.inl (short_a7_block_of_six h e hd)
end CFSG.Quasithin.ChapterC
