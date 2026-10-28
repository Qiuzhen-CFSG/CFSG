module

public import Theory.Alternating.Aut
public import Theory.SpecificGroups.Quaternion.PresentationHom
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Extending an alternating-group embedding across a transposition

An injective map from Aₙ, for n ≥ 4, extends to Sₙ when an ambient
involution induces the specified transposition action. We construct the
map from Aₙ ⋊ C₂, identify this semidirect product with the actual
permutation group using sign, and prove injectivity from the faithful
conjugation action of Sₙ on Aₙ. The image is exactly the join of the
given alternating image and the cyclic subgroup of the involution.

This is the semidirect-product step in Aschbacher–Smith, Lemma 2.5.26,
printed pp.568–569 of the combined 1 March 2004 manuscript. It uses no
surjectivity theorem for automorphisms of Aₙ. The conjugation faithfulness
and cyclic power maps are reused from the existing CFSG development.
-/

open Subgroup Equiv Equiv.Perm
open QuaternionGroup (cyclicPowerHom cyclicPowerHom_one)

namespace Theory.SpecificGroups.Alternating.TranspositionExtension

private abbrev C2 := Multiplicative (ZMod 2)

private def swapPower {n : ℕ} (a b : Fin n) : C2 →* Perm (Fin n) :=
  cyclicPowerHom 2 (swap a b) (by rw [pow_two, Equiv.swap_mul_self])

private abbrev swapAction {n : ℕ} (a b : Fin n) :
    C2 →* MulAut (alternatingGroup (Fin n)) :=
  MulAut.conjNormal.comp (swapPower a b)

private def standardMap {n : ℕ} (a b : Fin n) :
    alternatingGroup (Fin n) ⋊[swapAction a b] C2 →* Perm (Fin n) :=
  SemidirectProduct.lift (alternatingGroup (Fin n)).subtype (swapPower a b)
    (by intro c; ext k; rfl)

private theorem standardMap_apply {n : ℕ} (a b : Fin n)
    (p : alternatingGroup (Fin n) ⋊[swapAction a b] C2) :
    standardMap a b p = (p.left : Perm (Fin n)) * swapPower a b p.right := rfl

private theorem standardMap_bijective {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    Function.Bijective (standardMap a b) := by
  constructor
  · apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    rintro ⟨k, c⟩ hp
    change (k : Perm (Fin n)) * swapPower a b c = 1 at hp
    change ZMod 2 at c
    fin_cases c
    · have hk : k = 1 := by
        apply Subtype.ext
        change (k : Perm (Fin n)) * swapPower a b 1 = 1 at hp
        simpa only [map_one, mul_one, Subgroup.coe_one] using hp
      subst k
      rfl
    · have hp' : (k : Perm (Fin n)) * swap a b = 1 := by
        change (k : Perm (Fin n)) * swapPower a b (Multiplicative.ofAdd 1) = 1 at hp
        simpa only [swapPower, cyclicPowerHom_one] using hp
      have hs := congrArg sign hp'
      have hk := mem_alternatingGroup.mp k.property
      simp only [map_mul, hk, sign_swap hab, one_mul, map_one] at hs
      norm_num at hs
  · intro p
    rcases Int.units_eq_one_or (sign p) with hp | hp
    · refine ⟨SemidirectProduct.inl ⟨p, mem_alternatingGroup.mpr hp⟩, ?_⟩
      simp [standardMap]
    · let k : alternatingGroup (Fin n) := ⟨p * swap a b, by
        rw [mem_alternatingGroup, map_mul, hp, sign_swap hab]
        simp⟩
      refine ⟨SemidirectProduct.inl k *
        SemidirectProduct.inr (Multiplicative.ofAdd 1), ?_⟩
      simp [standardMap, swapPower, cyclicPowerHom_one, k, mul_assoc]

/-- A compatible involution extends an alternating embedding to an embedding
of the actual symmetric group, retaining both marked maps. -/
public theorem exists_embedding {G : Type*} [Group G] {n : ℕ} (hn : 4 ≤ n)
    (a b : Fin n) (hab : a ≠ b)
    (f : alternatingGroup (Fin n) →* G) (hf : Function.Injective f)
    (t : G) (ht : t ^ 2 = 1)
    (haction : ∀ k, f (MulAut.conjNormal (swap a b) k) = t * f k * t⁻¹) :
    ∃ F : Perm (Fin n) →* G, Function.Injective F ∧
      (∀ k : alternatingGroup (Fin n), F k = f k) ∧ F (swap a b) = t := by
  let g : C2 →* G := cyclicPowerHom 2 t ht
  have hcompat (c : C2) :
      f.comp (swapAction a b c).toMonoidHom = (MulAut.conj (g c)).toMonoidHom.comp f := by
    ext k
    change f (MulAut.conjNormal (swapPower a b c) k) = g c * f k * (g c)⁻¹
    change ZMod 2 at c
    fin_cases c
    · change f (MulAut.conjNormal (swapPower a b 1) k) = g 1 * f k * (g 1)⁻¹
      simp
    · change f (MulAut.conjNormal (swapPower a b (Multiplicative.ofAdd 1)) k) =
        g (Multiplicative.ofAdd 1) * f k * (g (Multiplicative.ofAdd 1))⁻¹
      simpa only [swapPower, g, cyclicPowerHom_one] using haction k
  let L := SemidirectProduct.lift f g hcompat
  let e := MulEquiv.ofBijective (standardMap a b) (standardMap_bijective a b hab)
  let F : Perm (Fin n) →* G := L.comp e.symm.toMonoidHom
  have hFk (k : alternatingGroup (Fin n)) : F k = f k := by
    have hk : e.symm k = SemidirectProduct.inl k := by
      apply e.injective
      simp [e, standardMap]
    change L (e.symm k) = f k
    rw [hk]
    exact SemidirectProduct.lift_inl _ _ _ _
  have hFt : F (swap a b) = t := by
    have ht' : e.symm (swap a b) = SemidirectProduct.inr (Multiplicative.ofAdd 1) := by
      apply e.injective
      simp [e, standardMap, swapPower, cyclicPowerHom_one]
    change L (e.symm (swap a b)) = t
    rw [ht']
    simp [L, g, cyclicPowerHom_one]
  refine ⟨F, ?_, hFk, hFt⟩
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro p hp
  have hFp : F p = 1 := hp
  have hconj : MulAut.conjNormal (H := alternatingGroup (Fin n)) p = 1 := by
    apply MulEquiv.ext
    intro k
    change MulAut.conjNormal p k = k
    apply hf
    calc
      f (MulAut.conjNormal p k) = F (p * (k : Perm (Fin n)) * p⁻¹) :=
        (hFk (MulAut.conjNormal p k)).symm
      _ = f k := by rw [map_mul, map_mul, map_inv, hFp, hFk]; simp
  exact (GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n hn)
    (hconj.trans (map_one _).symm)

/-- The marked extension has precisely the subgroup generated by its
alternating image and the marked involution as its image. -/
public theorem range_eq {G : Type*} [Group G] {n : ℕ}
    (a b : Fin n) (hab : a ≠ b) (f : alternatingGroup (Fin n) →* G)
    (F : Perm (Fin n) →* G) (t : G)
    (hFk : ∀ k : alternatingGroup (Fin n), F k = f k) (hFt : F (swap a b) = t) :
    F.range = f.range ⊔ zpowers t := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    rcases Int.units_eq_one_or (sign p) with hp | hp
    · rw [hFk ⟨p, mem_alternatingGroup.mpr hp⟩]
      exact mem_sup_left ⟨_, rfl⟩
    · let k : alternatingGroup (Fin n) := ⟨p * swap a b, by
        rw [mem_alternatingGroup, map_mul, hp, sign_swap hab]
        simp⟩
      have hp' : p = (k : Perm (Fin n)) * swap a b := by simp [k, mul_assoc]
      rw [hp', map_mul, hFk, hFt]
      exact mul_mem (mem_sup_left ⟨_, rfl⟩) (mem_sup_right (mem_zpowers t))
  · apply sup_le
    · rintro _ ⟨k, rfl⟩
      exact ⟨k, hFk k⟩
    · exact zpowers_le.mpr ⟨swap a b, hFt⟩

end Theory.SpecificGroups.Alternating.TranspositionExtension
