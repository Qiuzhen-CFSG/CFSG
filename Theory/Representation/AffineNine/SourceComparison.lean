module

public import Theory.Representation.AffineNine.Model
public import Theory.SpecificGroups.GL2.ThreeResidualImages
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.FieldTheory.Finiteness

/-!
# Marked comparison with the natural affine-nine models

An elementary nine-group with a self-centralizing, disjoint supplement has
its original supplement as the linear complement. A two-perfect actor of
image order 24 forces the determinant-one subgroup into this linear image.
The determinant quotient then leaves precisely the special and full natural
column models. No splitting or affine-model hypothesis is assumed.

Source application: Aschbacher--Smith, 15.4.10, printed p. 1159.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups IsMulCommutative
namespace Representation.AffineNine.SourceComparison

private def translationAutAdd (a : MulAut Translation) : Plane ≃+ Plane where
  toFun v := (a (Multiplicative.ofAdd v)).toAdd
  invFun v := (a.symm (Multiplicative.ofAdd v)).toAdd
  left_inv v := a.left_inv v
  right_inv v := a.right_inv v
  map_add' v w := a.map_mul v w

private def translationAutLinear : MulAut Translation ≃* (Plane ≃ₗ[ZMod 3] Plane) where
  toFun a := { translationAutAdd a with map_smul' := ZMod.map_smul (translationAutAdd a) }
  invFun a := a.toAddEquiv.toMultiplicative
  left_inv a := by ext; rfl
  right_inv a := by ext; rfl
  map_mul' a b := by ext; rfl

private def naturalActionEquiv : LinearGroup ≃* MulAut Translation :=
  GeneralLinearGroup.toLin.trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) Plane).trans
      translationAutLinear.symm)

private theorem naturalActionEquiv_apply (g : LinearGroup) :
    naturalActionEquiv g = naturalAction g := rfl

private theorem exists_coordinates {E : Type*} [Group E] [Finite E]
    [IsElementaryAbelian 3 E] (hE : Nat.card E = 9) :
    Nonempty (E ≃* Translation) := by
  classical
  have hpow : 3 ^ Module.finrank (ZMod 3) (Additive E) = 3 ^ 2 := by
    have hsize := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := Additive E)
    change Nat.card E = _ at hsize
    simpa only [Nat.card_zmod, hE, show (3 : ℕ) ^ 2 = 9 by decide] using hsize.symm
  have hdim : Module.finrank (ZMod 3) (Additive E) = 2 :=
    Nat.pow_right_injective (by decide : 1 < 3) hpow
  let b := Module.finBasisOfFinrankEq (ZMod 3) (Additive E) hdim
  exact ⟨b.equivFun.toAddEquiv.toMultiplicativeRight⟩

private def linearized {E : Type*} [Group E] (c : E ≃* Translation) :
    MulAut E ≃* LinearGroup := (MulAut.congr c).trans naturalActionEquiv.symm

private theorem linearized_apply {E : Type*} [Group E]
    (c : E ≃* Translation) (a : MulAut E) (v : E) :
    naturalAction (linearized c a) (c v) = c (a v) := by
  rw [← naturalActionEquiv_apply]
  change naturalActionEquiv (naturalActionEquiv.symm (MulAut.congr c a)) (c v) = _
  rw [naturalActionEquiv.apply_symm_apply]
  change c (a (c.symm (c v))) = _
  rw [c.symm_apply_apply]

private theorem special_or_full (L : Subgroup LinearGroup)
    (hSL : GeneralLinearGroup.threeSpecialLinear ≤ L) :
    L = GeneralLinearGroup.threeSpecialLinear ∨ L = ⊤ := by
  let d : LinearGroup →* (ZMod 3)ˣ := GeneralLinearGroup.det
  let : Fact (Nat.card (ZMod 3)ˣ).Prime := ⟨by
    rw [Nat.card_eq_fintype_card]
    decide⟩
  rcases (L.map d).eq_bot_or_eq_top_of_prime_card with hb | ht
  · exact Or.inl (le_antisymm ((map_eq_bot_iff L).mp hb) hSL)
  · right
    have he := congrArg (Subgroup.comap d) ht
    rw [comap_map_eq, comap_top] at he
    have hk : d.ker ≤ L := hSL
    rwa [sup_eq_left.mpr hk] at he

private theorem special_image {A : Type*} [Group A]
    (hp : IsPPerfect 2 A) (a : A →* LinearGroup) (hcard : Nat.card a.range = 24) :
    a.range = GeneralLinearGroup.threeSpecialLinear := by
  have hne : a.range ≠ ⊥ := by
    intro he
    have hc := card_eq_one.mpr he
    omega
  rcases GeneralLinearGroup.three_twoPerfect_subgroup a.range
    (hp.of_surjective a.rangeRestrict a.rangeRestrict_surjective) hne with hc | he
  · exfalso
    have he : (3 : ℕ) = 24 := hc.symm.trans hcard
    norm_num at he
  · exact he

private theorem complement_injective {D : Type*} [Group D]
    (E B : Subgroup D) [E.Normal]
    (hcent : centralizer (E : Set D) = E) (hdis : Disjoint E B) :
    Function.Injective ((MulAut.conjNormal : D →* MulAut E).comp B.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro b hb
  have hc : (b : D) ∈ centralizer (E : Set D) := by
    rw [← MulAut.conjNormal_ker_eq_centralizer E]
    exact hb
  have he : (b : D) ∈ E ⊓ B := ⟨hcent ▸ hc, b.property⟩
  have hz : (b : D) = 1 := by
    have hh := (disjoint_iff.mp hdis) ▸ he
    exact mem_bot.mp hh
  exact Subtype.ext hz

/-- Construct the natural semidirect model using the prescribed coordinates
and actual injective action of the original complement. Both embeddings are
retained pointwise. -/
theorem equiv_affine_of_complement {D : Type*} [Group D]
    (E B : Subgroup D) [E.Normal] (hjoin : E ⊔ B = ⊤) (hdis : Disjoint E B)
    (c : E ≃* Translation) (j : B →* LinearGroup)
    (hact : ∀ b : B, ∀ v : E,
      c (MulAut.conjNormal (b : D) v) = naturalAction (j b) (c v)) :
    ∃ f : D ≃* Affine j,
      (∀ v : E, f v = SemidirectProduct.inl (c v)) ∧
      ∀ b : B, f b = SemidirectProduct.inr b := by
  have hc : E.IsComplement' B := by
    refine ⟨mul_injective_of_disjoint hdis, ?_⟩
    intro d
    obtain ⟨v, hv, b, hb, he⟩ := mem_sup_of_normal_left.mp
      (show d ∈ E ⊔ B by rw [hjoin]; exact mem_top d)
    exact ⟨(⟨v, hv⟩, ⟨b, hb⟩), he⟩
  let φ : B →* MulAut E := E.normalizerMonoidHom.comp
    (inclusion (E.normalizer_eq_top ▸ le_top))
  let r : E ⋊[φ] B ≃* D := SemidirectProduct.mulEquivSubgroup hc
  let s : E ⋊[φ] B ≃* Affine j := SemidirectProduct.congr c (MulEquiv.refl B) (by
    intro b
    ext v : 1
    exact hact b v)
  let f : D ≃* Affine j := r.symm.trans s
  refine ⟨f, ?_, ?_⟩
  · intro v
    have hr : r (SemidirectProduct.inl v) = (v : D) := by
      change (v : D) * 1 = (v : D)
      exact mul_one _
    rw [← hr]
    change s (r.symm (r (SemidirectProduct.inl v))) = _
    rw [r.symm_apply_apply]
    rfl
  · intro b
    have hr : r (SemidirectProduct.inr b) = (b : D) := by
      change (1 : D) * b = (b : D)
      exact one_mul _
    rw [← hr]
    change s (r.symm (r (SemidirectProduct.inr b))) = _
    rw [r.symm_apply_apply]
    apply SemidirectProduct.ext <;> simp [s, SemidirectProduct.congr]

private theorem special_range :
    (SpecialLinearGroup.toGL : SpecialLinear →* LinearGroup).range =
      GeneralLinearGroup.threeSpecialLinear := by
  apply le_antisymm
  · rintro g ⟨s, rfl⟩
    exact SpecialLinearGroup.coeToGL_det s
  · intro g hg
    exact ⟨⟨g.val, (GeneralLinearGroup.three_mem_specialLinear g).mp hg⟩, Units.ext rfl⟩

private noncomputable def specialEmbedding : SpecialLinear ≃* GeneralLinearGroup.threeSpecialLinear :=
  (MonoidHom.ofInjective SpecialLinearGroup.toGL_injective).trans
    (MulEquiv.subgroupCongr special_range)

private theorem specialEmbedding_apply (s : SpecialLinear) :
    (specialEmbedding s : LinearGroup) = SpecialLinearGroup.toGL s := by
  simp only [specialEmbedding, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    MonoidHom.ofInjective_apply]

/-- An order-24 two-perfect action inside the original complement recognizes
one of the exact natural-column affine-nine models. This retains translations,
the complement and its action; the coordinates are constructed internally. -/
theorem special_or_full_of_marked_complement {D A : Type*}
    [Group D] [Finite D] [Group A]
    (E B : Subgroup D) [E.Normal] [IsElementaryAbelian 3 E]
    (hE : Nat.card E = 9) (hjoin : E ⊔ B = ⊤) (hdis : Disjoint E B)
    (hcent : centralizer (E : Set D) = E)
    (a : A →* D) (ha : a.range ≤ B) (hp : IsPPerfect 2 A)
    (hcard : Nat.card ((MulAut.conjNormal : D →* MulAut E).comp a).range = 24) :
    ∃ c : E ≃* Translation,
      (∃ (f : D ≃* Special) (b : B ≃* SpecialLinear),
        (∀ v : E, f v = SemidirectProduct.inl (c v)) ∧
        (∀ s : B, f s = SemidirectProduct.inr (b s)) ∧
        ∀ (s : B) (v : E), c (MulAut.conjNormal (s : D) v) =
          naturalAction (SpecialLinearGroup.toGL (b s)) (c v)) ∨
      (∃ (f : D ≃* Full) (b : B ≃* LinearGroup),
        (∀ v : E, f v = SemidirectProduct.inl (c v)) ∧
        (∀ s : B, f s = SemidirectProduct.inr (b s)) ∧
        ∀ (s : B) (v : E), c (MulAut.conjNormal (s : D) v) =
          naturalAction (b s) (c v)) := by
  obtain ⟨c⟩ := exists_coordinates hE
  let α := (MulAut.conjNormal : D →* MulAut E)
  let linearAction : D →* LinearGroup := (linearized c).toMonoidHom.comp α
  let j : B →* LinearGroup := linearAction.comp B.subtype
  have hj : Function.Injective j := (linearized c).injective.comp
    (complement_injective E B hcent hdis)
  have hact (b : B) (v : E) :
      c (MulAut.conjNormal (b : D) v) = naturalAction (j b) (c v) :=
    (linearized_apply c (α b) v).symm
  let ξ := linearAction.comp a
  have hξ : Nat.card ξ.range = 24 := by
    have he : ξ.range = ((α.comp a).range).map (linearized c).toMonoidHom := by
      change ((linearized c).toMonoidHom.comp (α.comp a)).range = _
      exact MonoidHom.range_comp _ _
    rw [he, ← hcard]
    exact (Nat.card_congr
      (((α.comp a).range).equivMapOfInjective (linearized c).toMonoidHom
        (linearized c).injective).toEquiv).symm
  have hSL : GeneralLinearGroup.threeSpecialLinear ≤ j.range := by
    rw [← special_image hp ξ hξ]
    rintro g ⟨x, rfl⟩
    exact ⟨⟨a x, ha ⟨x, rfl⟩⟩, rfl⟩
  obtain ⟨f0, hfE, hfB⟩ := equiv_affine_of_complement E B hjoin hdis c j hact
  let bj : B ≃* j.range := MonoidHom.ofInjective hj
  refine ⟨c, ?_⟩
  rcases special_or_full j.range hSL with hs | hf
  · left
    let b0 : B ≃* GeneralLinearGroup.threeSpecialLinear := bj.trans (MulEquiv.subgroupCongr hs)
    let b : B ≃* SpecialLinear := b0.trans specialEmbedding.symm
    have hb (s : B) : SpecialLinearGroup.toGL (b s) = j s := by
      have hh := congrArg Subtype.val (specialEmbedding.apply_symm_apply (b0 s))
      rw [specialEmbedding_apply] at hh
      simpa only [b, b0, bj, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
        MonoidHom.ofInjective_apply] using hh
    let r : Affine j ≃* Special := SemidirectProduct.congr (MulEquiv.refl Translation) b (by
      intro s
      ext v : 1
      change naturalAction (j s) v = naturalAction (SpecialLinearGroup.toGL (b s)) v
      rw [hb])
    refine ⟨f0.trans r, b, ?_, ?_, ?_⟩
    · intro v
      change r (f0 v) = _
      rw [hfE]
      apply SemidirectProduct.ext <;> simp [r, SemidirectProduct.congr]
    · intro s
      change r (f0 s) = _
      rw [hfB]
      rfl
    · intro s v
      rw [hb]
      exact hact s v
  · right
    let b : B ≃* LinearGroup := bj.trans ((MulEquiv.subgroupCongr hf).trans Subgroup.topEquiv)
    have hb (s : B) : b s = j s := rfl
    let r : Affine j ≃* Full := SemidirectProduct.congr (MulEquiv.refl Translation) b (by
      intro s
      ext v : 1
      change naturalAction (j s) v = naturalAction (b s) v
      rw [hb])
    refine ⟨f0.trans r, b, ?_, ?_, ?_⟩
    · intro v
      change r (f0 v) = _
      rw [hfE]
      apply SemidirectProduct.ext <;> simp [r, SemidirectProduct.congr]
    · intro s
      change r (f0 s) = _
      rw [hfB]
      rfl
    · intro s v
      rw [hb]
      exact hact s v

end Representation.AffineNine.SourceComparison
