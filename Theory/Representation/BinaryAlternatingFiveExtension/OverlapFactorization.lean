module
public import Theory.Representation.BinaryAlternatingFiveExtension.Automorphism
public import Theory.Representation.BinaryAlternatingFiveExtension.BorelEmbedding
public import Theory.Representation.BinaryAlternatingFiveExtension.BorelCohomology
public import GorensteinWalter.AutAlternatingFour
public import Theory.GroupTheory.Amalgam.RestrictionProduct

/-!
# Factoring the marked binary affine overlap automorphisms

An overlap automorphism preserving the four-dimensional translation module
induces an automorphism of A₄. Extend its realizing S₄ permutation to five
letters to obtain a compatible plane automorphism. After dividing out that
permutation, the module centralizer gives identity or the central twist.
The remaining cocycle is principal in the full four-letter permutation
module, hence extends to the whole affine A₅ plane by conjugation.

Thus the original discrepancy is a product of a plane restriction and the
identity or central twist. The last theorem constructs the exact endpoint
restriction factorization used in the ordinary unitary amalgam comparison,
retaining the order and inverse required for both commuting squares.

Source: Aschbacher--Smith 13.5.17, printed p.922, ordinary U₄(2) branch.
-/

public noncomputable section
open Subgroup
namespace BinaryPermutation.AlternatingFiveExtension.OverlapFactorization
open AlternatingFiveBorel

private def firstFour : Fin 4 ≃ {i : Fin 5 // i ≠ 4} where
  toFun i := ⟨i.castSucc, Fin.castSucc_ne_last i⟩
  invFun i := ⟨i.val.val, by
    have hn : i.val.val ≠ 4 := fun h => i.property (Fin.ext h)
    have := i.val.isLt
    omega⟩
  left_inv _ := by rfl
  right_inv _ := by rfl

def liftPerm : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 5) :=
  Equiv.Perm.extendDomainHom firstFour

theorem liftPerm_cast (σ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    liftPerm σ i.castSucc = (σ i).castSucc :=
  Equiv.Perm.extendDomain_apply_image σ firstFour i

theorem liftPerm_last (σ : Equiv.Perm (Fin 4)) : liftPerm σ 4=4 :=
  Equiv.Perm.extendDomain_apply_not_subtype σ firstFour (by simp)

theorem liftPerm_marking (a : alternatingGroup (Fin 4)) :
    liftPerm a.val = (marking a).val.val := by
  apply Equiv.ext
  intro i
  induction i using Fin.lastCases with
  | last => exact (liftPerm_last a.val).trans (marking a).property.symm
  | cast i => exact (liftPerm_cast a.val i).trans (marking_cast a i).symm

def actorPerm (σ : Equiv.Perm (Fin 4)) : MulAut B :=
  MulAut.congr marking (MulAut.conjNormal σ)

theorem actorPerm_val (σ : Equiv.Perm (Fin 4)) (b : B) :
    (actorPerm σ b).val = MulAut.conjNormal (liftPerm σ) b.val := by
  obtain ⟨a,rfl⟩ := marking.surjective b
  apply Subtype.ext
  simp only [actorPerm, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  change (marking (MulAut.conjNormal σ a)).val.val =
    liftPerm σ * (marking a).val.val * (liftPerm σ)⁻¹
  rw [←liftPerm_marking,←liftPerm_marking,←map_inv,←map_mul,←map_mul]
  rfl

def borelPermutation (σ : Equiv.Perm (Fin 4)) : MulAut BorelModel :=
  SemidirectProduct.congr (coreAction (liftPerm σ)) (actorPerm σ) (by
    intro b
    change (alternatingAction b.val).trans (coreAction (liftPerm σ)) =
      (coreAction (liftPerm σ)).trans (alternatingAction (actorPerm σ b).val)
    rw [actorPerm_val]
    exact standard_compatible (liftPerm σ) b.val)

theorem borelPermutation_right (σ : Equiv.Perm (Fin 4)) (x : BorelModel) :
    (borelPermutation σ x).right = actorPerm σ x.right := by rfl

theorem borelPermutation_plane (σ : Equiv.Perm (Fin 4)) (x : BorelModel) :
    standardAction (liftPerm σ) (borelEmbedding x) =
      borelEmbedding (borelPermutation σ x) := by
  apply SemidirectProduct.ext
  · rfl
  · exact (actorPerm_val σ x.right).symm

theorem actorPerm_surjective : Function.Surjective actorPerm := by
  intro β
  obtain ⟨σ,hσ⟩ := GroupTheory.AutAlternating.aut_alternatingGroup_four_bijective_conj.2
    ((MulAut.congr marking).symm β)
  refine ⟨σ,?_⟩
  change MulAut.congr marking (MulAut.conjNormal σ)=β
  rw [hσ,MulEquiv.apply_symm_apply]


theorem exists_quotient_action (α : MulAut BorelModel)
    (hN : ∀ x : BorelModel, x.right=1 → (α x).right=1) :
    ∃ β : MulAut B, ∀ x : BorelModel, (α x).right=β x.right := by
  let q : B →* B := SemidirectProduct.rightHom.comp
    (α.toMonoidHom.comp SemidirectProduct.inr)
  have hq (x : BorelModel) : (α x).right=q x.right := by
    have he : x=SemidirectProduct.inl x.left * SemidirectProduct.inr x.right :=
      SemidirectProduct.mk_eq_inl_mul_inr x.right x.left
    rw [he,map_mul,SemidirectProduct.mul_right,hN _ rfl,one_mul]
    rfl
  have hs : Function.Surjective q := by
    intro b
    obtain ⟨x,hx⟩ := α.surjective (SemidirectProduct.inr b)
    exact ⟨x.right,(hq x).symm.trans (congrArg SemidirectProduct.right hx)⟩
  let β : MulAut B := MulEquiv.ofBijective q ⟨Finite.injective_iff_surjective.mpr hs,hs⟩
  exact ⟨β,hq⟩

theorem exists_kernel_action (α : MulAut BorelModel)
    (hN : ∀ x : BorelModel, x.right=1 → (α x).right=1) :
    ∃ f : core (Fin 5) ≃+ core (Fin 5), ∀ v : core (Fin 5),
      α (SemidirectProduct.inl (Multiplicative.ofAdd v)) =
        SemidirectProduct.inl (Multiplicative.ofAdd (f v)) := by
  let f : core (Fin 5) →+ core (Fin 5) := {
    toFun v := (α (SemidirectProduct.inl (Multiplicative.ofAdd v))).left.toAdd
    map_zero' := by simp
    map_add' v w := by
      change ((α (SemidirectProduct.inl (Multiplicative.ofAdd v * Multiplicative.ofAdd w))).left).toAdd = _
      rw [map_mul,map_mul,SemidirectProduct.mul_left,hN _ rfl]
      simp }
  have he (v : core (Fin 5)) : α (SemidirectProduct.inl (Multiplicative.ofAdd v)) =
      SemidirectProduct.inl (Multiplicative.ofAdd (f v)) := by
    apply SemidirectProduct.ext
    · rfl
    · exact hN _ rfl
  have hi : Function.Injective f := by
    intro v w h
    have hh := (he v).trans ((congrArg (fun z => SemidirectProduct.inl (Multiplicative.ofAdd z)) h).trans (he w).symm)
    exact congrArg Multiplicative.toAdd (SemidirectProduct.inl_injective (α.injective hh))
  exact ⟨AddEquiv.ofBijective f ⟨hi,Finite.surjective_of_injective hi⟩,he⟩


open Theory.GroupTheory RankTwoAmalgam

theorem borelTwist_involutive : Function.Involutive Overlap.borelTwist := by
  intro x
  apply SemidirectProduct.ext
  · change Multiplicative.ofAdd (Overlap.twist (Overlap.twist x.left.toAdd))=x.left
    rw [Overlap.twist_involutive]
    rfl
  · rfl

theorem borelTwist_inl (v : core (Fin 5)) :
    Overlap.borelTwist (SemidirectProduct.inl (Multiplicative.ofAdd v)) =
      SemidirectProduct.inl (Multiplicative.ofAdd (Overlap.twist v)) := by rfl

theorem quotient_fixed_factor (γ : MulAut BorelModel)
    (hq : ∀ x : BorelModel, (γ x).right=x.right) :
    ∃ l : MulAut BorelModel, (l=1 ∨ l=Overlap.borelTwist) ∧
      Function.Involutive l ∧ ExtendsAcross borelEmbedding (γ*l) := by
  obtain ⟨f,hf⟩ := exists_kernel_action γ (fun x hx => (hq x).trans hx)
  have finish (l : MulAut BorelModel) (hl : l=1 ∨ l=Overlap.borelTwist)
      (hi : Function.Involutive l)
      (hV : ∀ n : V, (γ*l) (SemidirectProduct.inl n)=SemidirectProduct.inl n)
      (hlq : ∀ x : BorelModel, (l x).right=x.right) :
      ∃ l : MulAut BorelModel, (l=1 ∨ l=Overlap.borelTwist) ∧
        Function.Involutive l ∧ ExtendsAcross borelEmbedding (γ*l) := by
    obtain ⟨n,hn⟩ := BorelCohomology.automorphism_translation_correction (γ*l) hV
      (fun x => (hq (l x)).trans (hlq x))
    refine ⟨l,hl,hi,MulAut.conj (borelEmbedding (SemidirectProduct.inl n)),?_⟩
    intro x
    change borelEmbedding (SemidirectProduct.inl n) * borelEmbedding x *
      (borelEmbedding (SemidirectProduct.inl n))⁻¹ = borelEmbedding ((γ*l) x)
    rw [hn,map_mul,map_mul,map_inv]
  rcases Overlap.quotient_fixed_module_cases γ f hf hq with h|h
  · apply finish 1 (Or.inl rfl) (fun _ => rfl)
    · intro n
      simpa [h n.toAdd] using hf n.toAdd
    · exact fun _ => rfl
  · apply finish Overlap.borelTwist (Or.inr rfl) borelTwist_involutive
    · intro n
      have hn : n=Multiplicative.ofAdd n.toAdd := by simp
      rw [hn]
      change γ (Overlap.borelTwist (SemidirectProduct.inl (Multiplicative.ofAdd n.toAdd)))=_
      rw [borelTwist_inl,hf,h,Overlap.twist_involutive]
    · exact Overlap.borelTwist_right

theorem factorsThrough_of_preserves_translations {P : Type*} [Group P]
    (i : BorelModel →* P) (ht : ExtendsAcross i Overlap.borelTwist)
    (α : MulAut BorelModel)
    (hN : ∀ x : BorelModel, x.right=1 → (α x).right=1) :
    FactorsThrough (⟨i,borelEmbedding⟩ : RankTwoAmalgam P BorelModel AlternatingModel) α := by
  obtain ⟨β,hβ⟩ := exists_quotient_action α hN
  obtain ⟨σ,hσ⟩ := actorPerm_surjective β
  let θ := borelPermutation σ
  have hθ (x : BorelModel) : (θ x).right=β x.right := by
    rw [borelPermutation_right,hσ]
  let γ : MulAut BorelModel := θ⁻¹*α
  have hγ (x : BorelModel) : (γ x).right=x.right := by
    apply β.injective
    calc
      β ((γ x).right) = (θ (γ x)).right := (hθ (γ x)).symm
      _ = (α x).right := by simp [γ]
      _ = β x.right := hβ x
  obtain ⟨l,hl,hli,he⟩ := quotient_fixed_factor γ hγ
  have hp : ExtendsAcross borelEmbedding (α*l) := by
    have hθe : ExtendsAcross borelEmbedding θ := ⟨standardAction (liftPerm σ),borelPermutation_plane σ⟩
    have hh := (extensionSubgroup borelEmbedding).mul_mem hθe he
    change ExtendsAcross borelEmbedding (θ*(γ*l)) at hh
    simpa only [γ,←mul_assoc,mul_inv_cancel,one_mul] using hh
  have hlp : ExtendsAcross i l := by
    rcases hl with rfl|rfl
    · exact ⟨1,fun _ => rfl⟩
    · exact ht
  refine ⟨l,(α*l).symm,hlp,(extensionSubgroup borelEmbedding).inv_mem hp,?_⟩
  apply MulEquiv.ext
  intro x
  change α x = α (l (l x))
  rw [hli]

end BinaryPermutation.AlternatingFiveExtension.OverlapFactorization
