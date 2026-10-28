module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.NaturalLayer

/-!
# Whole-core recognition before the field restriction

If the intrinsic core is Frattini-small, it equals the moved central omega
layer. The original quotient marking and its natural section then give every
short-group clause and a model of the actual block conjugation module, over
a field of the original degree. This separates the whole-core assertion of
MS93 (3.6) from the field restriction in (3.7); neither assertion is assumed
to follow just from the existence of an initial natural layer.

Source: Meierfrankenfeld--Stellmacher (1993), (3.6), p.870;
Aschbacher--Smith C.1.30--32, pp.135--136.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)

include h

/-- All short-group clauses and the natural block model hold at the original
degree once the whole-core bound is established. The model uses the actual
two-core quotient and its conjugation action on the intrinsic moving section. -/
theorem Input.short_and_natural_of_frattini_small
    (hsmall : ⁅pCore 2 H,K⁆ ≤
      (frattini (pCore 2 H)).map (pCore 2 H).subtype ⊔ omegaCenterIn (pCore 2 H)) :
    IsShort K ∧ ∃ E : BinaryField, E.degree = n ∧
      IsLinearBlockModel K (binarySymplectic E) := by
  obtain ⟨hK,hC,hs,hq,_⟩ := h.component_image_structure
  let := hK
  let := hC
  let := hs
  let := hq
  let := h.component.perfect
  have hperfect : IsPPerfect 2 K := by
    rw [←h.residual_eq]
    exact isPPerfect_pResidual 2
  obtain ⟨he,helem,hcentral⟩ := intrinsic_core_of_frattini_small K hperfect hsmall
  obtain ⟨hi,E,hE,⟨e⟩⟩ := h.centralOmega_moved_natural
  have hfitK : generalizedFitting K = pCore 2 K := by
    apply le_antisymm _ ((pCore_le_fitting K 2).trans (fitting_le_generalizedFitting K))
    rw [pCore_subnormal_eq_comap 2 h.component.subnormal]
    apply map_le_iff_le_comap.mp
    rw [←h.fitting]
    exact generalizedFitting_map_subtype_le_of_isSubnormal K h.component.subnormal
  let q := QuotientGroup.mk' (pCore 2 H)
  let hk := (QuotientGroup.ker_mk' _).trans h.centralOmega_centralizer.symm
  refine ⟨⟨inferInstance,hperfect,hfitK,helem,hcentral,
    Or.inl (IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv h.component).symm),
    BlockMovingSection.irreducible_of_moving (omegaCenterIn (pCore 2 H)) K q
      (QuotientGroup.mk'_surjective _) hk he hi⟩,E,hE,?_⟩
  exact BlockMovingSection.model_of_moving (omegaCenterIn (pCore 2 H)) K q
    (QuotientGroup.mk'_surjective _) hk he
    (cComponentTwoCoreQuotientEquiv h.component) (fun _ => rfl) _ e

/-- The original degree-two branch is a block after whole-core recognition;
no separate shortness or conjugation-module assumption is needed. -/
theorem Input.block_of_degree_two_frattini_small (hn : n = 2)
    (hsmall : ⁅pCore 2 H,K⁆ ≤
      (frattini (pCore 2 H)).map (pCore 2 H).subtype ⊔ omegaCenterIn (pCore 2 H)) :
    IsSp4FourBlock K := by
  obtain ⟨hs,E,hE,ρ,hmodel,hact⟩ := h.short_and_natural_of_frattini_small hsmall
  refine ⟨hs,E.Carrier,inferInstance,inferInstance,?_,ρ,hmodel,hact⟩
  rw [E.card_eq,hE,hn]
  decide

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
