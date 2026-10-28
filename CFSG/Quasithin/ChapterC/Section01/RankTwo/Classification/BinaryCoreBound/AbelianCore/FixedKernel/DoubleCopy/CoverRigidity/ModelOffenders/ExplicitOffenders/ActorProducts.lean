module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.FixedKernel.DoubleCopy.CoverRigidity.ModelOffenders.Actors
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# Product identifications of the explicit cover actors

The projection shear identifies the mixed actor group with SL₃(2) × C₂.
Scalar mixing of the two covered coordinates identifies the doubled actor
group with SL₃(2) × SL₂(2). Both identifications act on the actual dual-cocycle
cover U; no auxiliary four-dimensional model is assumed. The covering
projection proves faithfulness and separates the two factors.

These are structural inputs to the independent offender-exclusion argument
supporting Aschbacher–Smith, combined manuscript (1 March 2004), C.1.34(2),(5),
printed pp.136–137, and I.1.5–6, printed p.408. They do not assert exclusion
of offenders or identify the full linear normalizer.
-/

public section
open Representation
namespace CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.DoubleCopy.CoverModels.ModelOffenders
noncomputable section

private def mixedShears : Multiplicative (ZMod 2) →* BinaryGL (U × V) where
  toFun c := shear (c.toAdd • projection.toLinearMap)
  map_one' := by ext x <;> simp [shear]
  map_mul' c d := by
    apply LinearEquiv.ext
    intro x
    apply Prod.ext
    · rfl
    · change x.2 + (c.toAdd + d.toAdd) • projection x.1 =
        (x.2 + d.toAdd • projection x.1) + c.toAdd • projection x.1
      simp only [add_smul]
      abel

private lemma mixedShears_range : mixedShears.range = Subgroup.zpowers mixedShear := by
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    have hc : c.toAdd = 0 ∨ c.toAdd = 1 := by
      have h : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
      exact h _
    rcases hc with hc | hc
    · have he : mixedShears c = 1 := by ext x <;> simp [mixedShears, shear, hc]
      rw [he]
      exact Subgroup.one_mem _
    · have he : mixedShears c = mixedShear := by ext x <;> simp [mixedShears, mixedShear, shear, hc]
      rw [he]
      exact Subgroup.mem_zpowers _
  · apply Subgroup.zpowers_le.mpr
    exact ⟨Multiplicative.ofAdd 1, by ext x <;> simp [mixedShears, mixedShear, shear]⟩

private lemma mixedShears_commute (g : MatrixGroup) (c : Multiplicative (ZMod 2)) :
    Commute (linearAction mixed g) (mixedShears c) := by
  apply LinearEquiv.ext
  intro x
  change (cover g x.1, base g (x.2 + c.toAdd • projection x.1)) =
    (cover g x.1, base g x.2 + c.toAdd • projection (cover g x.1))
  rw [map_add, map_smul, projection.isIntertwining]

/-- The product of the matrix action with the binary projection shear. -/
def mixedParam : MatrixGroup × Multiplicative (ZMod 2) →* BinaryGL (U × V) :=
  (linearAction mixed).noncommCoprod mixedShears mixedShears_commute

/-- The mixed product action in the original module coordinates. -/
lemma mixedParam_apply (g : MatrixGroup) (c : Multiplicative (ZMod 2)) (x : U × V) :
    mixedParam (g,c) x =
      (cover g x.1, base g x.2 + c.toAdd • projection (cover g x.1)) := by
  change (cover g x.1, base g (x.2 + c.toAdd • projection x.1)) = _
  rw [map_add, map_smul, projection.isIntertwining]

/-- The product parametrization has exactly the specified generated image. -/
lemma mixedParam_range : mixedParam.range = mixedActors := by
  rw [mixedParam, MonoidHom.noncommCoprod_range, mixedShears_range]
  rfl

/-- Every mixed actor has the stated action on the actual universal cover. -/
lemma mixedActors_normalForm (a : mixedActors) :
    ∃ g : MatrixGroup, ∃ c : ZMod 2, ∀ x : U × V,
      a.val x = (cover g x.1, base g x.2 + c • projection (cover g x.1)) := by
  have ha : a.val ∈ mixedParam.range := mixedParam_range.symm ▸ a.property
  obtain ⟨⟨g,c⟩, hg⟩ := ha
  refine ⟨g, c.toAdd, ?_⟩
  intro x
  rw [← hg]
  change (cover g x.1, base g (x.2 + c.toAdd • projection x.1)) = _
  rw [map_add, map_smul, projection.isIntertwining]

/-- The mixed projection shear has square one. -/
lemma mixedShear_sq : mixedShear ^ 2 = 1 := by
  ext x <;> simp [pow_two, mixedShear, shear, add_assoc, ZModModule.add_self]


private lemma base_injective : Function.Injective base := by
  intro g t h
  exact Matrix.SpecialLinearGroup.toLin'_injective
    (LinearEquiv.toLinearMap_injective h)

/-- The natural summand detects the matrix factor; surjectivity of the covering projection detects the shear factor. -/
lemma mixedParam_injective : Function.Injective mixedParam := by
  apply (injective_iff_map_eq_one mixedParam).mpr
  rintro ⟨g,c⟩ h
  have hg : g = 1 := by
    apply base_injective
    apply LinearMap.ext
    intro v
    have he := congrArg (fun a : BinaryGL (U × V) => (a (0,v)).2) h
    change base g (v + c.toAdd • projection 0) = v at he
    simpa using he
  subst g
  have hc : c = 1 := by
    obtain ⟨u, hu⟩ := projection_isCover.1 (fun _ => 1)
    have he := congrArg (fun a : BinaryGL (U × V) => (a (u,0)).2 0) h
    change (base 1 (0 + c.toAdd • projection u)) 0 = 0 at he
    simpa [hu] using he
  exact Prod.ext rfl hc

/-- An actual product identification of the generated mixed group. -/
def mixedActorEquiv : MatrixGroup × Multiplicative (ZMod 2) ≃* mixedActors :=
  (MonoidHom.ofInjective mixedParam_injective).trans
    (MulEquiv.subgroupCongr mixedParam_range)

/-- The displayed shear viewed as an element of the generated group. -/
@[expose] def mixedShearActor : mixedActors :=
  ⟨mixedShear, (le_sup_right : Subgroup.zpowers mixedShear ≤ mixedActors)
    (Subgroup.mem_zpowers mixedShear)⟩

/-- The shear remains an involution in the generated subgroup. -/
lemma mixedShearActor_sq : mixedShearActor ^ 2 = 1 := Subtype.ext mixedShear_sq

/-- The pointwise fixer of the natural summand is contained in the shear subgroup. -/
lemma mixedActor_fixes_natural (a : mixedActors)
    (ha : ∀ v : V, a.val (0,v) = (0,v)) : a ∈ Subgroup.zpowers mixedShearActor := by
  obtain ⟨g,c,hgc⟩ := mixedActors_normalForm a
  have hg : g = 1 := by
    apply base_injective
    apply LinearMap.ext
    intro v
    have he := congrArg Prod.snd ((hgc (0,v)).symm.trans (ha v))
    simpa using he
  subst g
  have hc : c = 0 ∨ c = 1 := by
    have h : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    exact h c
  rcases hc with rfl | rfl
  · have he : a = 1 := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      change a.val x = x
      simpa only [map_one, Module.End.one_apply, zero_smul, add_zero] using hgc x
    rw [he]
    exact Subgroup.one_mem _
  · have he : a = mixedShearActor := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      change a.val x = (x.1, x.2 + projection x.1)
      simpa only [map_one, Module.End.one_apply, one_smul] using hgc x
    rw [he]
    exact Subgroup.mem_zpowers _


/-- The product identification proves finiteness of the mixed actors. -/
instance mixedActors_finite : Finite mixedActors :=
  Finite.of_equiv (MatrixGroup × Multiplicative (ZMod 2)) mixedActorEquiv.toEquiv

/-- The special-linear group in degree two over the binary field. -/
abbrev MixingGroup := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)

private def coordinateAction : Representation (ZMod 2) MixingGroup (U × U) where
  toFun g :=
    ((g 0 0 • LinearMap.fst (ZMod 2) U U + g 0 1 • LinearMap.snd (ZMod 2) U U).prod
     (g 1 0 • LinearMap.fst (ZMod 2) U U + g 1 1 • LinearMap.snd (ZMod 2) U U))
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Prod.ext <;> simp
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    apply Prod.ext <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, add_smul, smul_add, mul_smul] <;> module

/-- The literal scalar mixing of the two covered coordinates. -/
def doubledMixing : MixingGroup →* BinaryGL (U × U) := linearAction coordinateAction

/-- The coordinate action formula, without choosing coordinates on U. -/
lemma doubledMixing_apply (g : MixingGroup) (x : U × U) :
    doubledMixing g x = (g 0 0 • x.1 + g 0 1 • x.2, g 1 0 • x.1 + g 1 1 • x.2) := by rfl

/-- The two-by-two matrix adding the first coordinate to the second. -/
@[expose] def shearMatrix : MixingGroup := ⟨!![1,0;1,1], by decide⟩
/-- The two-by-two coordinate exchange matrix. -/
@[expose] def swapMatrix : MixingGroup := ⟨!![0,1;1,0], by decide⟩

/-- The elementary coordinate matrix induces the specified doubled shear. -/
lemma doubledMixing_shear : doubledMixing shearMatrix = doubledShear := by
  apply LinearEquiv.ext
  intro x
  rw [doubledMixing_apply]
  change (1 • x.1 + 0 • x.2, 1 • x.1 + 1 • x.2) = (x.1, x.2+x.1)
  simp only [one_smul, zero_smul, add_zero, add_comm]

/-- The exchange matrix induces the specified doubled swap. -/
lemma doubledMixing_swap : doubledMixing swapMatrix = doubledSwap := by
  apply LinearEquiv.ext
  intro x
  rw [doubledMixing_apply]
  change (0 • x.1 + 1 • x.2, 1 • x.1 + 0 • x.2) = (x.2,x.1)
  simp only [one_smul, zero_smul, add_zero, zero_add]

/-- The six matrices in SL₂(2), checked exhaustively by the kernel. -/
lemma mixingGroup_cases (g : MixingGroup) :
    g = 1 ∨ g = shearMatrix ∨ g = swapMatrix ∨ g = shearMatrix * swapMatrix ∨
      g = swapMatrix * shearMatrix ∨ g = shearMatrix * swapMatrix * shearMatrix := by
  have h : ∀ g : MixingGroup,
    g = 1 ∨ g = shearMatrix ∨ g = swapMatrix ∨ g = shearMatrix * swapMatrix ∨
      g = swapMatrix * shearMatrix ∨ g = shearMatrix * swapMatrix * shearMatrix := by
    decide +kernel
  exact h g

/-- The two mixing generators generate exactly the SL₂(2) coordinate action. -/
lemma doubledMixing_range : doubledMixing.range =
    Subgroup.zpowers doubledShear ⊔ Subgroup.zpowers doubledSwap := by
  let K := Subgroup.zpowers doubledShear ⊔ Subgroup.zpowers doubledSwap
  have hs : doubledShear ∈ K := (le_sup_left : Subgroup.zpowers doubledShear ≤ K) (Subgroup.mem_zpowers _)
  have ht : doubledSwap ∈ K := (le_sup_right : Subgroup.zpowers doubledSwap ≤ K) (Subgroup.mem_zpowers _)
  apply le_antisymm
  · rintro _ ⟨g,rfl⟩
    rcases mixingGroup_cases g with rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simpa only [doubledMixing_shear] using hs
    · simpa only [doubledMixing_swap] using ht
    · simpa only [map_mul, doubledMixing_shear, doubledMixing_swap] using K.mul_mem hs ht
    · simpa only [map_mul, doubledMixing_shear, doubledMixing_swap] using K.mul_mem ht hs
    · simpa only [map_mul, doubledMixing_shear, doubledMixing_swap] using K.mul_mem (K.mul_mem hs ht) hs
  · refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact ⟨shearMatrix, doubledMixing_shear⟩
    · exact ⟨swapMatrix, doubledMixing_swap⟩

private lemma doubledMixing_commute (g : MatrixGroup) (h : MixingGroup) :
    Commute (linearAction doubled g) (doubledMixing h) := by
  apply LinearEquiv.ext
  intro x
  change (cover g (h 0 0 • x.1 + h 0 1 • x.2), cover g (h 1 0 • x.1 + h 1 1 • x.2)) =
    (h 0 0 • cover g x.1 + h 0 1 • cover g x.2,
      h 1 0 • cover g x.1 + h 1 1 • cover g x.2)
  simp only [map_add, map_smul]

/-- The commuting product of the covered matrix action and coordinate mixing. -/
def doubledParam : MatrixGroup × MixingGroup →* BinaryGL (U × U) :=
  (linearAction doubled).noncommCoprod doubledMixing doubledMixing_commute

/-- The doubled product action in the original module coordinates. -/
lemma doubledParam_apply (g : MatrixGroup) (h : MixingGroup) (x : U × U) :
    doubledParam (g,h) x =
      (h 0 0 • cover g x.1 + h 0 1 • cover g x.2,
        h 1 0 • cover g x.1 + h 1 1 • cover g x.2) := by
  change (cover g (h 0 0 • x.1 + h 0 1 • x.2),
    cover g (h 1 0 • x.1 + h 1 1 • x.2)) = _
  simp only [map_add, map_smul]

/-- The product image is exactly the specified doubled actor group. -/
lemma doubledParam_range : doubledParam.range = doubledActors := by
  rw [doubledParam, MonoidHom.noncommCoprod_range, doubledMixing_range]
  rfl

/-- Every doubled actor has this scalar-matrix action on the actual cover. -/
lemma doubledActors_normalForm (a : doubledActors) :
    ∃ g : MatrixGroup, ∃ h : MixingGroup, ∀ x : U × U,
      a.val x = (h 0 0 • cover g x.1 + h 0 1 • cover g x.2,
        h 1 0 • cover g x.1 + h 1 1 • cover g x.2) := by
  have ha : a.val ∈ doubledParam.range := doubledParam_range.symm ▸ a.property
  obtain ⟨⟨g,h⟩, hg⟩ := ha
  refine ⟨g,h, ?_⟩
  intro x
  rw [← hg]
  change (cover g (h 0 0 • x.1 + h 0 1 • x.2), cover g (h 1 0 • x.1 + h 1 1 • x.2)) = _
  simp only [map_add, map_smul]


/-- Off-diagonal entries detect the mixing factor; the covering projection detects the matrix factor. -/
lemma doubledParam_injective : Function.Injective doubledParam := by
  apply (injective_iff_map_eq_one doubledParam).mpr
  rintro ⟨g,h⟩ heq
  obtain ⟨u, hu⟩ := projection_isCover.1 (fun _ => 1)
  have hu0 : u ≠ 0 := by
    intro he
    have h1 := congrFun hu 0
    simp only [he, map_zero, Pi.zero_apply] at h1
    exact zero_ne_one h1
  have hgu : cover g u ≠ 0 := by
    intro hz
    exact hu0 ((linearAction cover g).injective (hz.trans (map_zero _).symm))
  have h01 : h 0 1 = 0 := by
    have he := congrArg (fun a : BinaryGL (U × U) => (a (0,u)).1) heq
    change cover g (h 0 0 • 0 + h 0 1 • u) = 0 at he
    simp only [smul_zero, zero_add, map_smul] at he
    exact (smul_eq_zero.mp he).resolve_right hgu
  have h10 : h 1 0 = 0 := by
    have he := congrArg (fun a : BinaryGL (U × U) => (a (u,0)).2) heq
    change cover g (h 1 0 • u + h 1 1 • 0) = 0 at he
    simp only [smul_zero, add_zero, map_smul] at he
    exact (smul_eq_zero.mp he).resolve_right hgu
  have hh : h = 1 := by
    have hdiag : ∀ h : MixingGroup, h 0 1 = 0 → h 1 0 = 0 → h = 1 := by decide +kernel
    exact hdiag h h01 h10
  subst h
  change linearAction doubled g * doubledMixing 1 = 1 at heq
  rw [map_one, mul_one] at heq
  have hg : g = 1 := by
    apply Matrix.SpecialLinearGroup.toLin'_injective
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := projection_isCover.1 v
    have he := congrArg (fun a : BinaryGL (U × U) => projection (a (w,0)).1) heq
    change projection (cover g w) = projection w at he
    change base g (projection w) = base 1 (projection w)
    rw [map_one, Module.End.one_apply]
    rw [projection.isIntertwining] at he
    exact he
  exact Prod.ext hg rfl

/-- An actual product identification of the generated doubled group. -/
def doubledActorEquiv : MatrixGroup × MixingGroup ≃* doubledActors :=
  (MonoidHom.ofInjective doubledParam_injective).trans
    (MulEquiv.subgroupCongr doubledParam_range)

/-- The product identification proves finiteness of the doubled actors. -/
instance doubledActors_finite : Finite doubledActors :=
  Finite.of_equiv (MatrixGroup × MixingGroup) doubledActorEquiv.toEquiv


/-- The mixed product equivalence retains the explicit operator. -/
lemma mixedActorEquiv_val (x : MatrixGroup × Multiplicative (ZMod 2)) :
    (mixedActorEquiv x).val = mixedParam x := by rfl

/-- The central generator corresponds to the actual projection shear. -/
lemma mixedActorEquiv_shear :
    mixedActorEquiv (1, Multiplicative.ofAdd 1) = mixedShearActor := by
  apply Subtype.ext
  rw [mixedActorEquiv_val]
  change linearAction mixed 1 * mixedShears (Multiplicative.ofAdd 1) = mixedShear
  rw [map_one, one_mul]
  ext x <;> simp [mixedShears, mixedShear, shear]

/-- The doubled product equivalence retains the explicit operator. -/
lemma doubledActorEquiv_val (x : MatrixGroup × MixingGroup) :
    (doubledActorEquiv x).val = doubledParam x := by rfl

/-- The coordinate mixing group has order six. -/
lemma mixingGroup_card : Nat.card MixingGroup = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- The generated mixed group has order 336. -/
lemma mixedActors_card : Nat.card mixedActors = 336 := by
  rw [← Nat.card_congr mixedActorEquiv.toEquiv, Nat.card_prod]
  change Nat.card MatrixGroup * Nat.card (ZMod 2) = 336
  rw [Matrix.PSL3Two.card_SL, Nat.card_zmod]

/-- The generated doubled group has order 1008. -/
lemma doubledActors_card : Nat.card doubledActors = 1008 := by
  rw [← Nat.card_congr doubledActorEquiv.toEquiv, Nat.card_prod,
    mixingGroup_card, Matrix.PSL3Two.card_SL]

end
end CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.DoubleCopy.CoverModels.ModelOffenders
