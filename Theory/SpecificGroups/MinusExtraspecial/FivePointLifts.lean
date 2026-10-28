module
public import Theory.GroupTheory.MinusExtraspecialA5Fusion.Model
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import all Theory.GroupTheory.MinusExtraspecialA5Fusion.Model
import all Theory.SpecificGroups.MinusExtraspecial.ModelFixedFour

/-!
# Cubic actions on the five singular points of the minus extraspecial core

Explicit involution representatives lift the five singular central cosets.
An automorphism whose cube is one fixes both lifts of every fixed point;
moving a point makes the quotient of its two lifts have order four.
Interchanging representatives retains the possible central factor. A faithful A₅ action is marked
by its actual alternating permutation action on these five points.

These facts supply the square construction in the arbitrary-source J₂
common-neighbor graph. Only the 32-element core and its five points are
calculated. Private bit coordinates are used only in proofs.

Source: Aschbacher, *Sporadic Groups* (1994), 47.8, p.265.
-/

@[expose] public section
namespace MinusExtraspecial.FivePointLifts
open Subgroup FixedFourCalculation FixedFourCalculation.Outside

def lift (i : Fin 5) : Model :=
  ![⟨.a 0, true, false⟩, ⟨.a 0, false, true⟩, ⟨.a 1, true, true⟩,
    ⟨.xa 0, true, true⟩, ⟨.xa 1, true, true⟩] i

theorem lift_sq (i : Fin 5) : lift i ^ 2 = 1 := by revert i; decide +kernel

theorem central_fixed (a : MulAut Model) : a (quaternion z) = quaternion z := by
  have hc : quaternion z ∈ center Model := (MinusExtraspecial.mem_center_iff _).mpr (Or.inr rfl)
  have h := (MinusExtraspecial.mem_center_iff _).mp ((MulEquivClass.apply_mem_center_iff a).mpr hc)
  exact h.resolve_left (by simpa using (show quaternion z ≠ 1 by decide +kernel))

theorem lift_image (a : MulAut Model) (i : Fin 5) :
    a (lift i) = lift (fivePointAction a i) ∨
      a (lift i) = quaternion z * lift (fivePointAction a i) := by
  have h := (action_eq_iff a i (fivePointAction a i)).mp rfl
  have hc : ∀ (x : Model) (j : Fin 5), encode x &&& 29 = rep j →
      x = lift j ∨ x = quaternion z * lift j := by decide +kernel
  exact hc _ _ (by
    have he : ∀ i, lift i = decode (rep i) := by decide +kernel
    simpa only [he] using h)

theorem cubic_fixed (a : MulAut Model) (ha : a ^ 3 = 1)
    (i : Fin 5) (hi : fivePointAction a i = i) : a (lift i) = lift i := by
  rcases lift_image a i with h | h
  · rwa [hi] at h
  · rw [hi] at h
    have hcube := DFunLike.congr_fun ha (lift i)
    have hz : quaternion z * quaternion z = 1 := by decide +kernel
    change a (a (a (lift i))) = lift i at hcube
    rw [h, map_mul, central_fixed, h, ← mul_assoc, hz, one_mul, h] at hcube
    have hh : quaternion z = 1 := mul_right_cancel (hcube.trans (one_mul _).symm)
    exact (show quaternion z ≠ 1 by decide +kernel) hh |>.elim

theorem moved_product_order (a : MulAut Model) (i : Fin 5)
    (hi : fivePointAction a i ≠ i) : orderOf (a (lift i) * (lift i)⁻¹) = 4 := by
  have hc : ∀ i j : Fin 5, i ≠ j →
      ((lift j * (lift i)⁻¹) ^ 2 ≠ 1 ∧ (lift j * (lift i)⁻¹) ^ 4 = 1) ∧
      (((quaternion z * lift j) * (lift i)⁻¹) ^ 2 ≠ 1 ∧
        ((quaternion z * lift j) * (lift i)⁻¹) ^ 4 = 1) := by decide +kernel
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime_pow (p := 2) (n := 1)
  · rcases lift_image a i with h | h
    · rw [h]; exact (hc i _ hi.symm).1.1
    · rw [h]; exact (hc i _ hi.symm).2.1
  · rcases lift_image a i with h | h
    · rw [h]; exact (hc i _ hi.symm).1.2
    · rw [h]; exact (hc i _ hi.symm).2.2

/-- Interchanging two singular lifts changes their product by at most the
central involution. This keeps track of the central term in ambient actions. -/
theorem lift_swap (i j : Fin 5) :
    lift i * lift j = lift j * lift i ∨
      lift i * lift j = lift j * lift i * quaternion z := by
  revert i j
  decide +kernel

private theorem faithful_points
    (φ : alternatingGroup (Fin 5) →* MulAut Model) (hφ : Function.Injective φ) :
    Function.Injective (fivePointAction.comp φ) := by
  let : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rcases (inferInstance : (fivePointAction.comp φ).ker.Normal).eq_bot_or_eq_top with h | h
  · exact h
  · have hle : φ.range ≤ (MulAut.conj : Model →* MulAut Model).range := by
      rintro _ ⟨a, rfl⟩
      rw [← action_kernel]
      exact show a ∈ (fivePointAction.comp φ).ker from h ▸ mem_top a
    have hc := Nat.card_le_card_of_injective _ (inclusion_injective hle)
    have hb := Nat.card_le_card_of_surjective _
      (MonoidHom.rangeRestrict_surjective (MulAut.conj : Model →* MulAut Model))
    rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv,
      nat_card_alternatingGroup] at hc
    rw [card_model] at hb
    norm_num [Nat.factorial] at hc
    change 60 ≤ Nat.card (MulAut.conj : Model →* MulAut Model).range at hc
    omega

/-- A faithful A₅ action on the core is the full alternating action on its
five singular points, with an actual marking of the acting group. -/
theorem exists_marking
    (φ : alternatingGroup (Fin 5) →* MulAut Model) (hφ : Function.Injective φ) :
    ∃ e : alternatingGroup (Fin 5) ≃* alternatingGroup (Fin 5),
      ∀ a, fivePointAction (φ a) = (e a : Equiv.Perm (Fin 5)) := by
  let f := fivePointAction.comp φ
  have heven (a : alternatingGroup (Fin 5)) : Equiv.Perm.sign (f a) = 1 := by
    have hk : (⊤ : Subgroup (alternatingGroup (Fin 5))) ≤ (Equiv.Perm.sign.comp f).ker := by
      rw [← commutator_alternatingGroup_eq_top (by simp)]
      exact Abelianization.commutator_subset_ker _
    exact hk (mem_top a)
  let fA : alternatingGroup (Fin 5) →* alternatingGroup (Fin 5) :=
    f.codRestrict _ heven
  have hf : Function.Injective fA := by
    intro a b h
    exact faithful_points φ hφ (congrArg Subtype.val h)
  exact ⟨MulEquiv.ofBijective fA
    ((Nat.bijective_iff_injective_and_card fA).mpr ⟨hf, rfl⟩), fun _ => rfl⟩

end MinusExtraspecial.FivePointLifts
