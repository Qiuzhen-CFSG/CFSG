module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.Parity
public import Mathlib.GroupTheory.Complement

/-!
# Extending a Frobenius-compatible Hall--Janko embedding

The literal degree-100 permutation extension splits over its specified odd
involution: multiplication identifies it with the semidirect product of the
original carrier and the two powers of that involution. We construct this
isomorphism using the proved parity and normalization calculations.

Given an injective inner homomorphism intertwining that involution with
coefficient Frobenius, a map of semidirect products constructs the required
outer embedding. Its injectivity follows from injectivity of the inner map
and nontriviality of Frobenius on F₄. Both markings are proved for the literal
maps in `G2FourModule.MarkedEmbedding`.

Source: Aschbacher--Smith, K.4.5, printed p.460/PDF p.471. This is a conditional
extension construction, not an existence theorem for the inner embedding.
The imported permutation and octonion modules retain their ATLAS attributions.
-/

@[expose] public noncomputable section
namespace Sporadic.LeechRelated.J2.G2FourModule.Embedding
open ExceptionalParabolics Atlas.G2.Natural.BinarySemilinear
open scoped Pointwise

abbrev Complement := Subgroup.zpowers involution

def complementInvolution : Complement := ⟨involution, Subgroup.mem_zpowers _⟩

theorem complementInvolution_ne_one : complementInvolution ≠ 1 := by
  intro h
  have hv : involution = 1 := congrArg Subtype.val h
  exact involution_not_mem_generated (hv.symm ▸ generated.one_mem)

theorem complementInvolution_mul_self : complementInvolution * complementInvolution = 1 :=
  Subtype.ext involution_mul_self

theorem complement_cases (x : Complement) : x = 1 ∨ x = complementInvolution := by
  classical
  have ht : involution ^ 2 = 1 := by simp [pow_two]
  have hne : involution ≠ 1 := fun h => involution_not_mem_generated (h ▸ generated.one_mem)
  have ho : orderOf involution = 2 := orderOf_eq_prime ht hne
  have hfin : IsOfFinOrder involution := isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, ht⟩
  have hx := x.property
  rw [hfin.mem_zpowers_iff_mem_range_orderOf, ho] at hx
  obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hx
  have hi' : i = 0 ∨ i = 1 := by have := Finset.mem_range.mp hi; omega
  rcases hi' with rfl | rfl
  · exact Or.inl (Subtype.ext (by simpa using heq.symm))
  · apply Or.inr
    apply Subtype.ext
    change (x : Equiv.Perm (Fin 100)) = involution
    simpa using heq.symm

theorem complement_normalizes : Complement ≤ Subgroup.normalizer (generated : Set _) :=
  Subgroup.zpowers_le.mpr involution_mem_normalizer

def complementAction : Complement →* MulAut Carrier :=
  generated.normalizerMonoidHom.comp (Subgroup.inclusion complement_normalizes)

abbrev Split := Carrier ⋊[complementAction] Complement

def splitToExtension : Split →* Extension :=
  (SemidirectProduct.monoidHomSubgroup complement_normalizes).codRestrict extension
    (fun x => Subgroup.mul_mem_sup x.left.property x.right.property)

theorem splitToExtension_bijective : Function.Bijective splitToExtension := by
  have hd : Disjoint generated Complement := Subgroup.disjoint_def.mpr (by
    intro x hx hc
    rcases complement_cases ⟨x, hc⟩ with h | h
    · exact congrArg Subtype.val h
    · have hh : x = involution := congrArg Subtype.val h
      exact (involution_not_mem_generated (hh ▸ hx)).elim)
  constructor
  · intro x y h
    have hp : (x.left, x.right) = (y.left, y.right) :=
      Subgroup.mul_injective_of_disjoint hd (congrArg Subtype.val h)
    apply SemidirectProduct.ext
    · exact congrArg Prod.fst hp
    · exact congrArg Prod.snd hp
  · intro x
    have hx : (x : Equiv.Perm (Fin 100)) ∈
        (generated : Set (Equiv.Perm (Fin 100))) * (Complement : Set _) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left generated Complement complement_normalizes]
      exact x.property
    obtain ⟨g, hg, c, hc, hgc⟩ := hx
    exact ⟨⟨⟨g, hg⟩, ⟨c, hc⟩⟩, Subtype.ext hgc⟩

def splitEquiv : Split ≃* Extension := MulEquiv.ofBijective splitToExtension splitToExtension_bijective

@[simp] theorem splitEquiv_inl (j : Carrier) :
    splitEquiv (SemidirectProduct.inl j) = intoExtension j := by
  apply Subtype.ext
  change (j : Equiv.Perm (Fin 100)) * 1 = j
  exact mul_one _

@[simp] theorem splitEquiv_inr :
    splitEquiv (SemidirectProduct.inr complementInvolution) = extensionInvolution := by
  apply Subtype.ext
  change 1 * involution = involution
  exact one_mul _

theorem fourFrobenius_mul_self : fourFrobenius * fourFrobenius = 1 := by
  ext a
  exact fourFrobenius_involutive a

theorem fourFrobenius_ne_one : fourFrobenius ≠ 1 := by
  classical
  intro h
  let := Fintype.ofFinite Four
  have ha (a : Four) : a = 0 ∨ a = 1 := by
    have hh := DFunLike.congr_fun h a
    change a ^ 2 = a at hh
    have hz : a * (a - 1) = 0 := by rw [mul_sub, ← pow_two, mul_one, hh, sub_self]
    exact (mul_eq_zero.mp hz).imp_right sub_eq_zero.mp
  have hs : (Finset.univ : Finset Four) ⊆ {0, 1} := by
    intro a _
    simpa using ha a
  have hc : Fintype.card Four ≤ 2 := (Finset.card_le_card hs).trans (by simp)
  rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by decide)] at hc
  norm_num at hc

def complementField : Complement →* (Four ≃+* Four) where
  toFun c := if c = 1 then 1 else fourFrobenius
  map_one' := if_pos rfl
  map_mul' c d := by
    rcases complement_cases c with rfl | rfl <;>
      rcases complement_cases d with rfl | rfl <;>
      simp [complementInvolution_ne_one, complementInvolution_mul_self, fourFrobenius_mul_self]

@[simp] theorem complementField_involution :
    complementField complementInvolution = fourFrobenius := by
  change (if complementInvolution = 1 then (1 : Four ≃+* Four) else fourFrobenius) = _
  exact if_neg complementInvolution_ne_one

theorem complementField_injective : Function.Injective complementField := by
  intro c d h
  rcases complement_cases c with rfl | rfl <;>
    rcases complement_cases d with rfl | rfl
  · rfl
  · exact (fourFrobenius_ne_one (by simpa using h.symm)).elim
  · exact (fourFrobenius_ne_one (by simpa using h)).elim
  · rfl

variable (f : Carrier →* M)
  (hf : Function.Injective f)
  (hσ : ∀ j, f (involutionAut j) = Atlas.G2.fieldEquiv fourFrobenius (f j))

def splitMap : Split →* OuterM :=
  SemidirectProduct.map f complementField (by
    intro c
    rcases complement_cases c with rfl | rfl
    · apply MonoidHom.ext
      intro j
      rfl
    · apply MonoidHom.ext
      intro j
      exact hσ j)

include hf in
theorem splitMap_injective : Function.Injective (splitMap f hσ) := by
  intro x y h
  apply SemidirectProduct.ext
  · exact hf (congrArg SemidirectProduct.left h)
  · exact complementField_injective (congrArg SemidirectProduct.right h)

/-- Construct the marked outer embedding from the equivariant inner map. -/
def markedOfEquivariant : MarkedEmbedding where
  inner := f
  inner_injective := hf
  outer := (splitMap f hσ).comp splitEquiv.symm.toMonoidHom
  outer_injective := (splitMap_injective f hf hσ).comp splitEquiv.symm.injective
  on_inner j := by
    change splitMap f hσ (splitEquiv.symm (intoExtension j)) = _
    rw [← splitEquiv_inl j, splitEquiv.symm_apply_apply]
    exact SemidirectProduct.map_inl _ _ _ _
  on_involution := by
    change splitMap f hσ (splitEquiv.symm extensionInvolution) = _
    rw [← splitEquiv_inr, splitEquiv.symm_apply_apply]
    exact (SemidirectProduct.map_inr _ _ _ _).trans (congrArg SemidirectProduct.inr complementField_involution)
end Sporadic.LeechRelated.J2.G2FourModule.Embedding
