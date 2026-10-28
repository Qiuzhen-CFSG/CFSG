module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.ElementarySixteen

/-!
# The local obstruction used in elementary-subgroup fusion

An elementary sixteen normalized by an element of order three must be the
binary factor E: conjugate it into the coordinate Sylow subgroup and exclude
F, whose normalizer has order 128. The three local vector classes also give
a multiplication obstruction: a product in the eight-element class cannot
have both factors in the six-element class.

These are the coordinate ingredients for an alternative proof of Janko,
*A characterization of the Mathieu simple groups, I*, J. Algebra 9 (1968),
Section 2, Lemma 4, pp.4–5. Finite calculations use kernel reduction.
-/

open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
open LocalModelDichotomy
local instance : DecidableEq TwistedModel := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) SemidirectProduct.ext_iff.symm
local instance : Fintype TwistedModel := Fintype.ofEquiv
  (BinaryFour × SymmetricFour) SemidirectProduct.equivProd.symm
local instance : DecidablePred (· ∈ modelE) := fun x =>
  inferInstanceAs (Decidable (x.right = 1))

private theorem model_card : Nat.card TwistedModel = 384 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- An element of order three in the normalizer distinguishes E from F. -/
public theorem model_elementary_sixteen_of_order_three_normalizer
    (A : Subgroup TwistedModel) (hA : IsElementaryAbelian 2 A)
    (hcard : Nat.card A = 16) (r : TwistedModel) (hr : orderOf r = 3)
    (hn : r ∈ normalizer (A : Set TwistedModel)) : A = modelE := by
  let := hA
  let T : Sylow 2 TwistedModel := Sylow.ofCard modelT (by
    rw [modelT_card, model_card]
    decide +kernel)
  obtain ⟨P, hAP⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq TwistedModel P T
  let f := (MulAut.conj g).toMonoidHom
  have hPmap : (P : Subgroup TwistedModel).map f = modelT :=
    congrArg Sylow.toSubgroup hg
  have hAT : A.map f ≤ modelT := (map_mono hAP).trans_eq hPmap
  have hAm : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  have hAc : Nat.card (A.map f) = 16 := by
    rw [← Nat.card_congr (A.equivMapOfInjective f (MulAut.conj g).injective).toEquiv, hcard]
  rcases model_elementary_sixteen (A.map f) hAT hAm hAc with he | he
  · let : modelE.Normal := by unfold modelE; infer_instance
    have heE : modelE.map f = modelE := Normal.map_conj_eq modelE g
    exact (map_injective (MulAut.conj g).injective) (he.trans heE.symm)
  · have hrN : f r ∈ normalizer (A.map f : Set TwistedModel) :=
      le_normalizer_map f (mem_map_of_mem f hn)
    rw [he, modelF_normalizer] at hrN
    have hdiv := modelT.orderOf_dvd_natCard hrN
    change orderOf ((MulAut.conj g) r) ∣ Nat.card modelT at hdiv
    rw [(MulAut.conj g).orderOf_eq r, hr, modelT_card] at hdiv
    norm_num at hdiv

private def six : Finset TwistedModel :=
  {z 2, z 3, z 2 * z 3, z 0 * z 2, z 0 * z 3, z 0 * z 2 * z 3}

private theorem modelE_partition (x : TwistedModel) (hx : x ∈ modelE) (hx1 : x ≠ 1) :
    x ∈ six ∨ IsConj x (z 0) ∨ IsConj x (z 1) := by
  have h : ∀ x : TwistedModel, x ∈ modelE → x ≠ 1 →
      x ∈ six ∨ ∃ s : SymmetricFour,
        (SemidirectProduct.inr s : TwistedModel) * x * (SemidirectProduct.inr s)⁻¹ = z 0 ∨
        (SemidirectProduct.inr s : TwistedModel) * x * (SemidirectProduct.inr s)⁻¹ = z 1 := by
    decide +kernel
  rcases h x hx hx1 with hs | ⟨s, hs | hs⟩
  · exact Or.inl hs
  · exact Or.inr (Or.inl (isConj_iff.mpr ⟨_, hs⟩))
  · exact Or.inr (Or.inr (isConj_iff.mpr ⟨_, hs⟩))

private theorem six_conj (x : TwistedModel) (hx : x ∈ six) : IsConj x (z 2) := by
  have h : ∀ x : TwistedModel, x ∈ six → ∃ s : SymmetricFour,
      (SemidirectProduct.inr s : TwistedModel) * x * (SemidirectProduct.inr s)⁻¹ = z 2 := by
    decide +kernel
  obtain ⟨s, hs⟩ := h x hx
  exact isConj_iff.mpr ⟨_, hs⟩

private theorem six_product_ne_z_one : ∀ x ∈ six, ∀ y ∈ six, x * y ≠ z 1 := by
  decide +kernel


/-- The three source classes exhaust the nonidentity vectors. -/
public theorem modelE_three_classes (x : TwistedModel) (hx : x ∈ modelE) (hx1 : x ≠ 1) :
    IsConj x (z 0) ∨ IsConj x (z 1) ∨ IsConj x (z 2) := by
  rcases modelE_partition x hx hx1 with hs | h0 | h1
  · exact Or.inr (Or.inr (six_conj x hs))
  · exact Or.inl h0
  · exact Or.inr (Or.inl h1)

/-- A product equal to printed z₂ has a factor in one of the first two classes. -/
public theorem modelE_product_z_one (x y : TwistedModel)
    (hx : x ∈ modelE) (hy : y ∈ modelE) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hxy : x * y = z 1) :
    IsConj x (z 0) ∨ IsConj x (z 1) ∨ IsConj y (z 0) ∨ IsConj y (z 1) := by
  rcases modelE_partition x hx hx1 with hs | h0 | h1
  · rcases modelE_partition y hy hy1 with ht | h0 | h1
    · exact (six_product_ne_z_one x hs y ht hxy).elim
    · exact Or.inr (Or.inr (Or.inl h0))
    · exact Or.inr (Or.inr (Or.inr h1))
  · exact Or.inl h0
  · exact Or.inr (Or.inl h1)

/-- Both factors of z₁ = z₃(z₁z₃) lie in the six-element class. -/
public theorem z_zero_mul_z_two_conj : IsConj (z 0 * z 2) (z 2) :=
  six_conj _ (by simp [six])

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
