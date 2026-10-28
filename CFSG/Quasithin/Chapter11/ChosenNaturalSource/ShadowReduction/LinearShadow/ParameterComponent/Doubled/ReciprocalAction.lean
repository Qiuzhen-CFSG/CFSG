module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.PlaneRecognition
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.SmallNormalizer
public import Theory.Representation.BinaryConjugationSection.NormalizerAction

/-!
# Constructing the reciprocal natural action on the original doubled section

Faithful section coordinates extend to the full normalizer. Surjectivity of
the original SL₃ quotient identifies its image exactly with the identical
natural component. Normalization of the original L therefore puts the actual
actor image in that component's binary normalizer. The small-codimension
calculation then forces natural placement, and the two literal centralizer
bounds construct full plane shears. No shear action or matrix placement is
assumed.

Source: Aschbacher--Smith, 11.3.6, printed pp.772--773.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.SL3DoubledNaturalOffenders
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
namespace ReciprocalAction
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable [Algebra (ZMod 2) F]
variable {G : Type*} [Group G] [Finite G] {A W L : Subgroup G}

omit [CharP F 2] in
private theorem fixed_corank (e : W ≃* Multiplicative (Space F))
    (hn : A ≤ normalizer (W : Set G)) (f : A →* Ambient F)
    (he : ∀ a : A, ∀ w : W,
      action F (f a) (e w).toAdd = (e (W.normalizerMonoidHom (inclusion hn a) w)).toAdd) :
    fixedCodim (action F) f.range = ChapterE.subgroupCorank W (W ⊓ centralizer (A : Set G)) := by
  have hfix (w : W) : (e w).toAdd ∈ fixedSpace (action F) f.range ↔
      (w : G) ∈ centralizer (A : Set G) := by
    constructor
    · intro hw a ha
      have hh := (he ⟨a,ha⟩ w).symm.trans (hw ⟨_,⟨⟨a,ha⟩,rfl⟩⟩)
      have hh' := congrArg Subtype.val (e.injective (Multiplicative.toAdd.injective hh))
      exact mul_inv_eq_iff_eq_mul.mp hh'
    · intro hw x
      obtain ⟨a,ha⟩ := x.property
      change action F (x : Ambient F) (e w).toAdd = (e w).toAdd
      rw [← ha,he]
      congr 2
      apply Subtype.ext
      change (a:G)*(w:G)*(a:G)⁻¹=(w:G)
      rw [hw a a.property,mul_inv_cancel_right]
  let U := fixedSpace (action F) f.range
  let C := (centralizer (A : Set G)).subgroupOf W
  let j : C ≃ U :=
    { toFun w := ⟨(e w.val).toAdd,(hfix w.val).mpr w.property⟩
      invFun w := ⟨e.symm (Multiplicative.ofAdd w.val),
        (hfix _).mp (by simpa only [MulEquiv.apply_symm_apply,toAdd_ofAdd] using w.property)⟩
      left_inv := fun w => Subtype.ext (e.symm_apply_apply w.val)
      right_inv := fun w => Subtype.ext (congrArg Multiplicative.toAdd
        (e.apply_symm_apply (Multiplicative.ofAdd w.val))) }
  have hc : Nat.card C = Nat.card U := Nat.card_congr j
  have hw : Nat.card W = Nat.card (Space F) := Nat.card_congr e.toEquiv
  have h₁ := Submodule.card_eq_card_quotient_mul_card U
  have h₂ := Subgroup.card_eq_card_quotient_mul_card_subgroup C
  have hq : Nat.card (Space F ⧸ U) = Nat.card (W ⧸ C) := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := C))
    calc
      _ = Nat.card (Space F) := by rw [hc,mul_comm,← h₁]
      _ = Nat.card W := hw.symm
      _ = _ := h₂
  have hd := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Space F ⧸ U)
  rw [Nat.card_zmod] at hd
  unfold ChapterE.subgroupCorank
  rw [inf_relIndex_left,relIndex,index_eq_card,← hq,hd,Nat.log_pow (by decide)]
  rfl

/-- The actual normalizer action preserves the marked SL₃ image, and small
fixed codimension forces its elementary actors into that image. -/
theorem naturalAction_of_section [IsElementaryAbelian 2 A]
    (q : L →* SL(3,F)) (hq : Function.Surjective q)
    (c : BinaryConjugationSection L W ⊥ ((representation F).comp q))
    (hNL : normalizer (W : Set G) ≤ normalizer (L : Set G))
    (hAW : A ≤ normalizer (W : Set G)) {n : ℕ} (hF : Nat.card F = 2^n)
    (hc : ChapterE.subgroupCorank W (W ⊓ centralizer (A : Set G)) < 3*n) :
    Nonempty (PlaneRecognition.NaturalAction A W F) := by
  have hi : Function.Injective c.coordinates := by
    apply c.coordinates.ker_eq_bot_iff.mp
    rw [c.kernel_eq,bot_subgroupOf]
  let e := MulEquiv.ofBijective c.coordinates ⟨hi,c.onto⟩
  let N := normalizer (W : Set G)
  let σ : N →* Ambient F :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Space F)).symm.toMonoidHom.comp
      (BinaryConjugationSection.normalizerAction c.coordinates ⟨hi,c.onto⟩)
  have hσ (a : N) (w : W) : action F (σ a) (e w).toAdd =
      (e (W.normalizerMonoidHom a w)).toAdd :=
    BinaryConjugationSection.normalizerAction_coordinates c.coordinates ⟨hi,c.onto⟩ a w
  have hL (l : L) : σ (inclusion c.normalized l) = (representation F).asGroupHom (q l) := by
    apply Units.ext
    exact BinaryConjugationSection.normalizerAction_restrict c hi l
  have himage : (L.subgroupOf N).map σ = component F := by
    apply le_antisymm
    · rintro _ ⟨l,hl,rfl⟩
      have hh := hL ⟨l,hl⟩
      exact ⟨q ⟨l,hl⟩,hh.symm⟩
    · rintro _ ⟨g,rfl⟩
      obtain ⟨l,rfl⟩ := hq g
      exact ⟨inclusion c.normalized l,l.property,hL l⟩
  have hN : ∀ a : N, σ a ∈ SL3DoubledNaturalOffenders.normalizer F := by
    intro a
    rw [SL3DoubledNaturalOffenders.normalizer,← himage]
    apply (L.subgroupOf N).le_normalizer_map σ
    apply mem_map_of_mem
    apply mem_normalizer_iff.mpr
    intro l
    exact mem_normalizer_iff.mp (hNL a.property) l
  let f := σ.comp (inclusion hAW)
  have hf (a : A) (w : W) : action F (f a) (e w).toAdd =
      (e (W.normalizerMonoidHom (inclusion hAW a) w)).toAdd := hσ _ _
  have hc' : fixedCodim (action F) f.range < 3*n := by
    rw [fixed_corank e hAW f hf]
    exact hc
  let : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hC : f.range ≤ component F := SmallNormalizer.elementary_le_component hF f.range
    (by rintro b ⟨a,rfl⟩; exact hN _) hc'
  let j : SL(3,F) ≃* component F := MonoidHom.ofInjective
    (show Function.Injective (representation F).asGroupHom from
      fun _ _ he => representation_injective F (congrArg Units.val he))
  let a := j.symm.toMonoidHom.comp (f.codRestrict _ (fun x => hC ⟨x,rfl⟩))
  refine ⟨⟨hAW,e,a,?_⟩⟩
  intro x w
  have ha : (representation F).asGroupHom (a x) = f x :=
    congrArg Subtype.val (j.apply_symm_apply _)
  have he := hf x w
  rw [← ha] at he
  exact he.symm

/-- Both numerical equations now construct full plane shears on the literal
section. Neither natural placement of the reciprocal actor nor shear
surjectivity is an input. -/
theorem shears_of_section [IsElementaryAbelian 2 A]
    (q : L →* SL(3,F)) (hq : Function.Surjective q)
    (c : BinaryConjugationSection L W ⊥ ((representation F).comp q))
    (hNL : normalizer (W : Set G) ≤ normalizer (L : Set G))
    (hAW : A ≤ normalizer (W : Set G)) {n : ℕ} (hn : 0<n) (hF : Nat.card F = 2^n)
    (hr : 2*n ≤ ChapterE.subgroupCorank A (A ⊓ centralizer (W : Set G)))
    (hc : ChapterE.subgroupCorank W (W ⊓ centralizer (A : Set G)) ≤ 2*n) :
    Nonempty (ShearCoordinates A W F) := by
  obtain ⟨d⟩ := naturalAction_of_section q hq c hNL hAW hF (by omega)
  exact d.shearCoordinates_of_coranks hn hF hr hc

end ReciprocalAction

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
