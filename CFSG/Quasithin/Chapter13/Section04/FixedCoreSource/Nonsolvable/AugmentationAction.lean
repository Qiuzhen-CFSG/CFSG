module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Normalizer
public import Theory.Representation.BinaryPermutation.SixCoreNormalizer
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupTheory.PCoreActionCardKernel
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The original augmentation action of the normalizer and LT

The five-dimensional marking extends to N_G(L): conjugation induces an
automorphism of the literal characteristic quotient L/O₂,Z(L), and the
normalizer of its augmentation action consists of six-letter permutations.
Faithfulness of that permutation action identifies the kernel with C_N(V).

In the ordinary A₆ row, restrict to the original LT. Its component image is
A₆, and LT/L is a two-group, so counting the component kernel makes the
whole kernel a two-group. The reverse inclusion follows because the chosen
module lies in the reduced module. Thus its kernel is exactly O₂(LT).
The earlier structural normalizer premise is discharged at this application;
no four-dimensional subgroup or split augmentation module is assumed.

Source: Aschbacher–Smith, the paragraph preceding Notation 13.2.1,
printed p.877, used in 13.2.2(6–7) and 13.4.10.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private def coreCoordinates {W : Type*} [Group W]
    (c : W ≃* Multiplicative (BinaryPermutation.core (Fin 6))) :
    MulAut W →* (BinaryPermutation.core (Fin 6) ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 6)) where
  toFun f := by
    let a := (AddEquiv.additiveMultiplicative (G := BinaryPermutation.core (Fin 6))).symm.trans
      (((MulAut.congr c) f).toAdditive.trans (AddEquiv.additiveMultiplicative (G := BinaryPermutation.core (Fin 6))))
    exact { a with map_smul' := ZMod.map_smul a }
  map_one' := by
    apply LinearEquiv.ext
    intro v
    change (c (c.symm (Multiplicative.ofAdd v))).toAdd = v
    rw [c.apply_symm_apply]
    rfl
  map_mul' f g := by
    apply LinearEquiv.ext
    intro v
    change (c (f (g (c.symm (Multiplicative.ofAdd v))))).toAdd =
      (c (f (c.symm (c (g (c.symm (Multiplicative.ofAdd v))))))).toAdd
    rw [c.symm_apply_apply]

variable (D : ChosenModule T L V) (m : CoreMarking D)
  (hn : normalizer (L : Set G) ≤ normalizer (V : Set G))

private def fullCoreAction : normalizer (L : Set G) →*
    (BinaryPermutation.core (Fin 6) ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 6)) :=
  (coreCoordinates m.coordinate).comp (V.normalizerMonoidHom.comp (inclusion hn))

omit [Finite G] in
private theorem fullCoreAction_inner (l : L) (v : BinaryPermutation.core (Fin 6)) :
    fullCoreAction D m hn (inclusion L.le_normalizer l) v =
      BinaryPermutation.coreRepresentation (Fin 6)
        (m.quotient (QuotientGroup.mk' (centralCore L) l)).val v := by
  change (m.coordinate (V.normalizerMonoidHom ⟨l.val,D.normalizes l.property⟩ (m.coordinate.symm (Multiplicative.ofAdd v)))).toAdd = _
  rw [m.equivariant,m.coordinate.apply_symm_apply]
  rfl

private def quotientAction : normalizer (L : Set G) →* MulAut (alternatingGroup (Fin 6)) := by
  let : (centralCore L).Characteristic :=
    inferInstanceAs (centralPreimage (pCore 2 L)).Characteristic
  exact (MulAut.congr m.quotient).toMonoidHom.comp
    ((quotientAut (centralCore L)).comp L.normalizerMonoidHom)

omit [Finite G] in
private theorem quotientAction_apply (x : normalizer (L : Set G)) (l : L) :
    quotientAction D m x (m.quotient (QuotientGroup.mk' (centralCore L) l)) =
      m.quotient (QuotientGroup.mk' (centralCore L) (L.normalizerMonoidHom x l)) := by
  let : (centralCore L).Characteristic :=
    inferInstanceAs (centralPreimage (pCore 2 L)).Characteristic
  change m.quotient (quotientAut _ _ (m.quotient.symm (m.quotient _))) = _
  rw [m.quotient.symm_apply_apply,quotientAut_apply_mk]

omit [Finite G] in
private theorem fullCoreAction_intertwines (x : normalizer (L : Set G))
    (a : alternatingGroup (Fin 6)) (v : BinaryPermutation.core (Fin 6)) :
    fullCoreAction D m hn x (BinaryPermutation.coreRepresentation (Fin 6) a.val v) =
      BinaryPermutation.coreRepresentation (Fin 6) (quotientAction D m x a).val
        (fullCoreAction D m hn x v) := by
  obtain ⟨q,rfl⟩ := m.quotient.surjective a
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (centralCore L) q
  rw [quotientAction_apply,←fullCoreAction_inner D m hn,
    ←fullCoreAction_inner D m hn]
  change (fullCoreAction D m hn x * fullCoreAction D m hn (inclusion L.le_normalizer l)) v =
    (fullCoreAction D m hn (inclusion L.le_normalizer (L.normalizerMonoidHom x l)) *
      fullCoreAction D m hn x) v
  rw [←map_mul,←map_mul]
  congr 2
  apply Subtype.ext
  change x.val * l.val = (x.val*l.val*x.val⁻¹)*x.val
  group

omit [Finite G] in
/-- Extend the actual augmentation marking to the full original normalizer.
Its restriction to L is the original L/centralCore L projection. -/
theorem exists_core_normalizer_permutation :
    ∃ q : normalizer (L : Set G) →* Equiv.Perm (Fin 6),
      (∀ (x : normalizer (L : Set G)) (v : V),
        (m.coordinate (V.normalizerMonoidHom (inclusion hn x) v)).toAdd =
          BinaryPermutation.coreRepresentation (Fin 6) (q x) (m.coordinate v).toAdd) ∧
      (∀ l : L, q (inclusion L.le_normalizer l) =
        (m.quotient (QuotientGroup.mk' (centralCore L) l)).val) ∧
      q.ker = (centralizer (V : Set G)).subgroupOf (normalizer (L : Set G)) := by
  classical
  have hex (x : normalizer (L : Set G)) := BinaryPermutation.SixCoreNormalizer.normalizer
    (fullCoreAction D m hn x) (quotientAction D m x) (fullCoreAction_intertwines D m hn x)
  choose p hp using hex
  have unique (a b : Equiv.Perm (Fin 6))
      (he : ∀ v, BinaryPermutation.coreRepresentation (Fin 6) a v =
        BinaryPermutation.coreRepresentation (Fin 6) b v) : a = b :=
    BinaryPermutation.SixCoreNormalizer.action_injective (LinearMap.ext he)
  let q : normalizer (L : Set G) →* Equiv.Perm (Fin 6) := {
    toFun := p
    map_one' := unique _ _ (fun v => by rw [←hp,map_one,map_one]; rfl)
    map_mul' := fun a b => unique _ _ (fun v => by
      rw [←hp,map_mul,LinearEquiv.mul_apply,hp,hp,map_mul,Module.End.mul_apply]) }
  have hq (x : normalizer (L : Set G)) (v : BinaryPermutation.core (Fin 6)) :
      fullCoreAction D m hn x v = BinaryPermutation.coreRepresentation (Fin 6) (q x) v := hp x v
  have he (x : normalizer (L : Set G)) (v : V) :
      (m.coordinate (V.normalizerMonoidHom (inclusion hn x) v)).toAdd =
        BinaryPermutation.coreRepresentation (Fin 6) (q x) (m.coordinate v).toAdd := by
    have hh := hq x (m.coordinate v).toAdd
    change (m.coordinate (V.normalizerMonoidHom _ (m.coordinate.symm (m.coordinate v)))).toAdd = _ at hh
    simpa only [m.coordinate.symm_apply_apply] using hh
  refine ⟨q,he,?_,?_⟩
  · intro l
    apply unique
    intro v
    rw [←hq,fullCoreAction_inner]
  · ext x
    change q x = 1 ↔ x.val ∈ centralizer (V : Set G)
    constructor
    · intro hx v hv
      have hh := he x ⟨v,hv⟩
      rw [hx,map_one,Module.End.one_apply] at hh
      have hc := congrArg Subtype.val (m.coordinate.injective (Multiplicative.toAdd.injective hh))
      change x.val*v*x.val⁻¹ = v at hc
      exact (mul_inv_eq_iff_eq_mul.mp hc).symm
    · intro hx
      apply unique
      intro w
      obtain ⟨v,rfl⟩ := m.coordinate.surjective (Multiplicative.ofAdd w)
      have hv : V.normalizerMonoidHom (inclusion hn x) v = v := by
        apply Subtype.ext
        change x.val*v.val*x.val⁻¹ = v.val
        rw [←hx v.val v.property,mul_inv_cancel_right]
      change BinaryPermutation.coreRepresentation (Fin 6) (q x) (m.coordinate v).toAdd =
        BinaryPermutation.coreRepresentation (Fin 6) 1 (m.coordinate v).toAdd
      rw [←he,hv,map_one,Module.End.one_apply]

omit hn in
/-- The ordinary row gives the actual LT action with precisely its two-core
as kernel, while retaining the original augmentation coordinates. -/
theorem exists_core_product_permutation
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    let X := L ⊔ (T : Subgroup G)
    ∃ q : X →* Equiv.Perm (Fin 6),
      (∀ (x : X) (v : V),
        (m.coordinate (V.normalizerMonoidHom
          ⟨x.val,(sup_le D.normalizes ((structural G T L h).2.2 V D).1) x.property⟩ v)).toAdd =
          BinaryPermutation.coreRepresentation (Fin 6) (q x) (m.coordinate v).toAdd) ∧
      (∀ l : L, q (inclusion le_sup_left l) =
        (m.quotient (QuotientGroup.mk' (centralCore L) l)).val) ∧
      (L.subgroupOf X).map q = alternatingGroup (Fin 6) ∧
      q.ker = pCore 2 X := by
  let X := L ⊔ (T : Subgroup G)
  have hn := normalizer_component_le_module h structural D m
  obtain ⟨q,hq,hqL,hker⟩ := exists_core_normalizer_permutation D m hn
  have hXN : X ≤ normalizer (L : Set G) := sup_le L.le_normalizer D.sylow_normalizes_component
  let f := q.comp (inclusion hXN)
  have hfL (l : L) : f (inclusion (show L ≤ X from le_sup_left) l) =
      (m.quotient (QuotientGroup.mk' (centralCore L) l)).val := hqL l
  let N := L.subgroupOf X
  have him : N.map f = alternatingGroup (Fin 6) := by
    apply le_antisymm
    · rintro a ⟨x,hx,rfl⟩
      have hh := hfL ⟨x.val,hx⟩
      change f x = _ at hh
      rw [hh]
      exact (m.quotient (QuotientGroup.mk' (centralCore L) ⟨x.val,hx⟩)).property
    · intro a ha
      obtain ⟨w,hw⟩ := m.quotient.surjective ⟨a,ha⟩
      obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (centralCore L) w
      exact ⟨inclusion le_sup_left l,l.property,(hfL l).trans (congrArg Subtype.val hw)⟩
  let : N.Normal := normal_subgroupOf_of_le_normalizer hXN
  have hquot : IsPGroup 2 (X ⧸ N) := by
    apply isPGroup_quotient_of_sup_eq_top N ((T : Subgroup G).subgroupOf X) T.isPGroup'.comap_subtype
    rw [←subgroupOf_sup (show L ≤ X from le_sup_left) (show (T : Subgroup G) ≤ X from le_sup_right),subgroupOf_self]
  have hfP : IsPGroup 2 f.ker := by
    apply MonoidHom.isPGroup_ker_of_card_image_eq_core_quotient f N hquot
    rw [him]
    let c : N ≃* L := subgroupOfEquivOfLe (show L ≤ X from le_sup_left)
    let cq : N ⧸ pCore 2 N ≃* L ⧸ pCore 2 L :=
      QuotientGroup.congr _ _ c (pCore_map_iso 2 c)
    exact (Nat.card_congr (cq.trans eL).toEquiv).symm
  refine ⟨f,?_,hfL,him,le_antisymm (le_sSup ⟨inferInstance,hfP⟩) ?_⟩
  · intro x v
    exact hq (inclusion hXN x) v
  · intro x hx
    have hxC : x.val ∈ centralizer (V : Set G) :=
      D.core_centralizes (mem_map.mpr ⟨x,hx,rfl⟩)
    change q (inclusion hXN x) = 1
    change inclusion hXN x ∈ q.ker
    rw [hker]
    exact hxC

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
