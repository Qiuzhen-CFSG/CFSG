module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleG2Model
public import Theory.Representation.FirstCohomologyDuality.Indecomposable
public import Theory.ElementaryAbelian.EightQuotientRank
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerFixedLine

/-!
# Fixed-space bounds for the chosen central cover

An equivariant identification of the literal chosen central quotient with a
natural module makes the chosen module a perfect central cover. First
cohomology of the dual bounds its fixed kernel. A Sylow subgroup of L inside
T maps onto a Sylow subgroup of the model actor, and the kernel-image formula
then bounds C_V(T) by the product of that kernel and the natural fixed space.

The maps below retain the original quotient L/O₂(L) and the conjugation action
on V. The G₂(2) and L₃(2) normalizer branches instantiate both numerical bounds.
Source: Aschbacher–Smith C.1.7 and 12.2.16, pp.123,800.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
open Representation.OneCohomology
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {A W : Type*} [Group A] [Finite A] [AddCommGroup W] [Module (ZMod 2) W]
variable [FiniteDimensional (ZMod 2) W] {σ : Representation (ZMod 2) A W}
namespace ChosenCover
variable (D : ChosenModule T L V) (e : ActionEquiv D.centralQuotientAction σ)
def action : Representation (ZMod 2) A D.space :=
  D.quotientAction.comp e.groupEquiv.symm.toMonoidHom

omit [Finite A] [FiniteDimensional (ZMod 2) W] in
theorem action_apply (q : L ⧸ pCore 2 L) (v : D.space) :
    action D e (e.groupEquiv q) v = D.quotientAction q v := by
  change D.quotientAction (e.groupEquiv.symm (e.groupEquiv q)) v = _
  rw [e.groupEquiv.symm_apply_apply]

def projection : (action D e).IntertwiningMap σ :=
  (e.linearEquiv.toLinearMap.comp (G2WeylModel.Fixed D).mkQ).intertwiningMap_of_isIntertwiningMap _ _ (by
    intro g v
    obtain ⟨q,rfl⟩ := e.groupEquiv.surjective g
    change e.linearEquiv ((G2WeylModel.Fixed D).mkQ (action D e (e.groupEquiv q) v)) = _
    rw [action_apply]
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
    exact e.intertwines (QuotientGroup.mk' (pCore 2 L) l) ((G2WeylModel.Fixed D).mkQ v))

omit [Finite A] [FiniteDimensional (ZMod 2) W] in
theorem projection_ker : (projection D e).toLinearMap.ker = G2WeylModel.Fixed D := by
  ext v
  change e.linearEquiv (Submodule.Quotient.mk v) = 0 ↔ _
  rw [← map_zero e.linearEquiv, e.linearEquiv.injective.eq_iff,Submodule.Quotient.mk_eq_zero]

omit [Finite A] [FiniteDimensional (ZMod 2) W] in
theorem isCover : IsCover (projection D e) := by
  refine ⟨e.linearEquiv.surjective.comp (G2WeylModel.Fixed D).mkQ_surjective, ?_, ?_⟩
  · rw [projection_ker]
    intro v hv g
    obtain ⟨q,rfl⟩ := e.groupEquiv.surjective g
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
    rw [action_apply]
    exact Subtype.ext (hv ((subgroupOfEquivOfLe
      (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).symm l))
  · have hle : subspaceCommutator D.quotientAction ⊤ ⊤ ≤ Coinvariants.ker (action D e) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨q, _, v, _, rfl⟩
      have hh := Coinvariants.sub_mem_ker (ρ := action D e) (e.groupEquiv q) v
      rwa [action_apply] at hh
    rw [D.quotientAction_irrPlus.choose_spec.1] at hle
    exact top_unique hle

omit e [Finite A] [FiniteDimensional (ZMod 2) W] in
def fixedEquiv : G2WeylModel.Fixed D ≃ (V ⊓ centralizer (L : Set G) : Subgroup G) where
  toFun v := ⟨D.spaceEquiv (Multiplicative.ofAdd v.val), (D.spaceEquiv _).property, by
    intro l hl
    have hh := v.property ((subgroupOfEquivOfLe
      (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).symm ⟨l,hl⟩)
    have hc := congrArg (fun w : Additive (ReducedModule (L ⊔ (T : Subgroup G))) =>
      (w.toMul.val : G)) hh
    rw [D.spaceEquiv_apply]
    exact mul_inv_eq_iff_eq_mul.mp hc⟩
  invFun v := ⟨(D.spaceEquiv.symm ⟨v,v.property.1⟩).toAdd, by
    intro l
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    have hv := (D.spaceEquiv_apply (D.spaceEquiv.symm ⟨v,v.property.1⟩).toAdd).symm.trans
      (congrArg Subtype.val (D.spaceEquiv.apply_symm_apply ⟨v,v.property.1⟩))
    change (l.val.val : G) * (((D.spaceEquiv.symm ⟨v,v.property.1⟩).toAdd).val.toMul.val : G) *
      (l.val.val : G)⁻¹ = (((D.spaceEquiv.symm ⟨v,v.property.1⟩).toAdd).val.toMul.val : G)
    simp only [hv]
    exact mul_inv_eq_iff_eq_mul.mpr (v.property.2 l l.property)⟩
  left_inv v := by apply Subtype.ext; exact congrArg Multiplicative.toAdd (D.spaceEquiv.symm_apply_apply _)
  right_inv v := by
    apply Subtype.ext
    change (D.spaceEquiv (D.spaceEquiv.symm ⟨v,v.property.1⟩) : G) = v
    exact congrArg Subtype.val (D.spaceEquiv.apply_symm_apply _)

include D e in
theorem fixed_card_eq_two (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hH : Module.finrank (ZMod 2) (H1 σ.dual) ≤ 1) :
    Nat.card (V ⊓ centralizer (L : Set G) : Subgroup G) = 2 := by
  have hk := (finrank_ker_le_H1_of_cover (projection D e) (isCover D e)).trans hH
  rw [projection_ker] at hk
  have hp : 0 < Module.finrank (ZMod 2) (G2WeylModel.Fixed D) :=
    Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr (G2WeylModel.fixed_ne_bot D hne))
  rw [←Nat.card_congr (fixedEquiv D),Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
    show Module.finrank (ZMod 2) (G2WeylModel.Fixed D) = 1 by omega,pow_one]

def point : V →* Multiplicative W :=
  (AddMonoidHom.toMultiplicative (projection D e).toLinearMap.toAddMonoidHom).comp D.spaceEquiv.symm.toMonoidHom

omit [Finite A] [FiniteDimensional (ZMod 2) W] in
/-- The natural point is the projection in the original chosen coordinates. -/
theorem point_toAdd (v : V) :
    (point D e v).toAdd = projection D e (D.spaceEquiv.symm v).toAdd := by
  rfl

omit [Finite A] [FiniteDimensional (ZMod 2) W] in
theorem point_ker : (point D e).ker = (centralizer (L : Set G)).subgroupOf V := by
  ext v
  change Multiplicative.ofAdd (projection D e (D.spaceEquiv.symm v).toAdd) = 1 ↔ _
  have hh := congrArg (fun N : Submodule (ZMod 2) D.space => (D.spaceEquiv.symm v).toAdd ∈ N)
    (projection_ker D e)
  change (projection D e (D.spaceEquiv.symm v).toAdd = 0) = _ at hh
  rw [show (Multiplicative.ofAdd (projection D e (D.spaceEquiv.symm v).toAdd) = 1) ↔
    projection D e (D.spaceEquiv.symm v).toAdd = 0 from Iff.rfl, hh]
  constructor
  · intro hv l hl
    have hc := hv ((subgroupOfEquivOfLe
      (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).symm ⟨l,hl⟩)
    have hc' := congrArg (fun w : Additive (ReducedModule (L ⊔ (T : Subgroup G))) =>
      (w.toMul.val : G)) hc
    have he := (D.spaceEquiv_apply (D.spaceEquiv.symm v).toAdd).symm.trans
      (congrArg Subtype.val (D.spaceEquiv.apply_symm_apply v))
    change l * ((D.spaceEquiv.symm v).toAdd.val.toMul.val : G) * l⁻¹ =
      ((D.spaceEquiv.symm v).toAdd.val.toMul.val : G) at hc'
    rw [he] at hc'
    exact mul_inv_eq_iff_eq_mul.mp hc'
  · intro hv l
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    have he := (D.spaceEquiv_apply (D.spaceEquiv.symm v).toAdd).symm.trans
      (congrArg Subtype.val (D.spaceEquiv.apply_symm_apply v))
    change (l.val.val : G) * ((D.spaceEquiv.symm v).toAdd.val.toMul.val : G) * (l.val.val : G)⁻¹ =
      ((D.spaceEquiv.symm v).toAdd.val.toMul.val : G)
    rw [he]
    exact mul_inv_eq_iff_eq_mul.mpr (hv l l.property)

omit [Finite A] [FiniteDimensional (ZMod 2) W] in
theorem point_conjugate (l : L) (v : V) :
    (point D e (V.normalizerMonoidHom ⟨l,D.normalizes l.property⟩ v)).toAdd =
      σ (e.groupEquiv (QuotientGroup.mk' (pCore 2 L) l)) (point D e v).toAdd := by
  have hc : (D.spaceEquiv.symm (V.normalizerMonoidHom ⟨l,D.normalizes l.property⟩ v)).toAdd =
      D.chosenAction l (D.spaceEquiv.symm v).toAdd := by
    apply Multiplicative.ofAdd.injective
    apply D.spaceEquiv.injective
    apply Subtype.ext
    change (D.spaceEquiv (D.spaceEquiv.symm _) : G) = _
    rw [D.spaceEquiv.apply_symm_apply,D.spaceEquiv_apply]
    have he := (D.spaceEquiv_apply (D.spaceEquiv.symm v).toAdd).symm.trans
      (congrArg Subtype.val (D.spaceEquiv.apply_symm_apply v))
    change (l:G) * (v:G) * (l:G)⁻¹ = (l:G) * ((D.spaceEquiv.symm v).toAdd.val.toMul.val : G) * (l:G)⁻¹
    rw [he]
  change projection D e ((D.spaceEquiv.symm _).toAdd) = _
  rw [hc,← D.quotientAction_mk,← action_apply D e]
  exact (projection D e).isIntertwining _ _ _ _


include D e in
omit [Finite A] in
theorem sylow_fixed_card_le_four
    (hfixed : Nat.card (V ⊓ centralizer (L : Set G) : Subgroup G) = 2)
    (hsmall : ∀ S : Sylow 2 A, Nat.card (fixedSpace σ (S : Subgroup A)) ≤ 2) :
    Nat.card (V ⊓ centralizer (T : Set G) : Subgroup G) ≤ 4 := by
  let : Finite W := Module.finite_of_finite (ZMod 2)
  let H := L ⊔ (T : Subgroup G)
  let X := L.subgroupOf H
  let : X.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  obtain ⟨R,hR⟩ := (T.subtype le_sup_right).exists_subgroupOf_eq_of_normal X
  let eL : X ≃* L := subgroupOfEquivOfLe (le_sup_left : L ≤ H)
  let P := R.mapSurjective (f := eL.toMonoidHom) eL.surjective
  have hP : ∀ l ∈ (P : Subgroup L), (l : G) ∈ (T : Subgroup G) := by
    rintro l ⟨r,hr,rfl⟩
    rw [hR] at hr
    exact hr
  let q : L →* A := e.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective _)
  let S := P.mapSurjective hq
  let B := (centralizer (T : Set G)).subgroupOf V
  have heB : Nat.card B = Nat.card (V ⊓ centralizer (T : Set G) : Subgroup G) := by
    rw [←card_map_of_injective V.subtype_injective,subgroupOf_map_subtype,inf_comm]
  have hBker : Nat.card (B ⊓ (point D e).ker : Subgroup V) ≤ 2 := by
    have hC : Nat.card (point D e).ker = 2 := by
      rw [point_ker,←card_map_of_injective V.subtype_injective,subgroupOf_map_subtype,inf_comm]
      exact hfixed
    exact (card_le_of_le inf_le_right).trans_eq hC
  have himage : Nat.card (B.map (point D e)) ≤ 2 := by
    let f : B.map (point D e) → fixedSpace σ (S : Subgroup A) := fun v =>
      ⟨v.val.toAdd, by
        intro a
        obtain ⟨l,hl,he⟩ := a.property
        obtain ⟨w,hw,hew⟩ := v.property
        have hc : V.normalizerMonoidHom ⟨l,D.normalizes l.property⟩ w = w := by
          apply Subtype.ext
          exact mul_inv_eq_iff_eq_mul.mpr (hw l (hP l hl))
        have hh := point_conjugate D e l w
        rw [hc] at hh
        change σ a.val v.val.toAdd = v.val.toAdd
        change (point D e w).toAdd = σ (q l) (point D e w).toAdd at hh
        rw [he,hew] at hh
        exact hh.symm⟩
    have hf : Function.Injective f := by
      intro v w hh
      apply Subtype.ext
      have hval : v.val.toAdd = w.val.toAdd :=
        congrArg (fun z : fixedSpace σ (S : Subgroup A) => z.val) hh
      exact Multiplicative.toAdd.injective hval
    exact (Nat.card_le_card_of_injective f hf).trans (hsmall S)
  have hc := IsElementaryAbelian.card_inf_ker_mul_card_map B (point D e)
  rw [←heB]
  nlinarith [Nat.mul_le_mul hBker himage]

end ChosenCover
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
