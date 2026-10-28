module
public import Theory.SpecificGroups.SymmetricFive.OuterFourIntersection
public import Theory.SpecificGroups.SymmetricFive.SylowNormalIntersection
public import Theory.SpecificGroups.SymmetricFive.WreathComponents
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# The marked plane kernel in a symmetric-five action

An elementary subgroup of a Sylow two-subgroup of S5 has order at most
four. If it acts nontrivially on a Sylow-invariant subspace, a nontrivial
subgroup fixing that subspace is its order-two pointwise kernel.
Normalization by the whole Sylow subgroup then places it in A5.
All normalization is relative to the given Sylow, and the original action
and its subspace are retained.

Source application: Aschbacher--Smith 14.3.23(2)(ii) and 14.3.25,
printed pp.1000--1001, with the original marked seed plane.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender
namespace Theory.SpecificGroups.SymmetricFive
variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]

/-- A nontrivial elementary actor fixing a Sylow-stable plane, inside a
Sylow-normal elementary subgroup acting nontrivially on that plane, is the
order-two pointwise kernel and belongs to the alternating residual. -/
theorem marked_plane_kernel (e : D ≃* Equiv.Perm (Fin 5))
    (ρ : Representation (ZMod 2) D W) (U : Submodule (ZMod 2) W)
    (S : Sylow 2 D) (X A : Subgroup D) [IsElementaryAbelian 2 X]
    (hXS : X ≤ (S : Subgroup D))
    (hSN : (S : Subgroup D) ≤ normalizer (X : Set D))
    (hSU : ∀ s ∈ S, ∀ w ∈ U, ρ s w ∈ U)
    (hAX : A ≤ X) (hne : A ≠ ⊥)
    (hAU : ∀ a ∈ A, ∀ w ∈ U, ρ a w = w)
    (hXU : ¬ U ≤ fixedSpace ρ X) :
    Nat.card A = 2 ∧ A ≤ solvableResidual D := by
  let Q := subspaceKernel ρ U X
  have hAQ : A ≤ Q := fun a ha => ⟨hAX ha,hAU a ha⟩
  have hQX : Q ≤ X := subspaceKernel_le ρ U X
  have hQne : Q ≠ ⊥ := fun he => hne (bot_unique (he ▸ hAQ))
  have hQP : 1 < Nat.card Q := Q.one_lt_card_iff_ne_bot.mpr hQne
  have hXc : Nat.card X ≤ 4 := by
    let X' := X.map e.toMonoidHom
    let : IsElementaryAbelian 2 X' := IsElementaryAbelian.map e.toMonoidHom
    have h := OuterFourIntersection.elementary_card_le_four (S.mapSurjective e.surjective)
      X' (map_mono hXS)
    rwa [card_map_of_injective e.injective] at h
  have hQc : Nat.card Q < 4 := by
    by_contra hh
    have he : Q = X := eq_of_le_of_card_ge hQX (by omega)
    apply hXU
    intro w hw x
    have hx : (x:D) ∈ Q := by rw [he]; exact x.property
    exact hx.2 w hw
  have hQcard : Nat.card Q = 2 := by
    obtain ⟨n,hn⟩ := ((IsElementaryAbelian.isPGroup 2 X).to_le hQX).exists_card_eq
    have hn2 : n < 2 := by
      by_contra h
      have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n by omega)
      rw [←hn] at hp
      omega
    have hn1 : n = 1 := by
      by_contra h
      have hn0 : n = 0 := by omega
      rw [hn0,pow_zero] at hn
      omega
    simpa only [hn1,pow_one] using hn
  have hAeq : A = Q := eq_of_le_of_card_ge hAQ (by
    rw [hQcard]
    exact A.one_lt_card_iff_ne_bot.mpr hne)
  have hQN : (S : Subgroup D) ≤ normalizer (Q : Set D) := by
    intro s hs
    apply mem_normalizer_iff.mpr
    intro a
    constructor
    · intro ha
      refine ⟨(mem_normalizer_iff.mp (hSN hs) a).mp ha.1,?_⟩
      intro w hw
      have hi := hSU s⁻¹ ((S : Subgroup D).inv_mem hs) w hw
      simp only [map_mul, Module.End.mul_apply,ha.2 _ hi]
      rw [← Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
    · intro ha
      refine ⟨(mem_normalizer_iff.mp (hSN hs) a).mpr ha.1,?_⟩
      intro w hw
      have hh := congrArg (ρ s⁻¹) (ha.2 (ρ s w) (hSU s hs w hw))
      simpa only [map_mul,Module.End.mul_apply,←Module.End.mul_apply,←map_mul,
        inv_mul_cancel,mul_inv_cancel,mul_one,one_mul,map_one,Module.End.one_apply, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left] using hh
  have hAc : Nat.card A = 2 := hAeq ▸ hQcard
  have hAN : (S : Subgroup D) ≤ normalizer (A : Set D) := hAeq.symm ▸ hQN
  let A' := A.map e.toMonoidHom
  have hA'c : Nat.card A' = 2 := (card_map_of_injective e.injective).trans hAc
  have hn' : A' ≠ ⊥ := by intro hh; rw [hh,card_bot] at hA'c; omega
  have hmeet : A' ⊓ alternatingGroup (Fin 5) ≠ ⊥ :=
    SylowNormalIntersection.inf_alternating_ne_bot (S.mapSurjective e.surjective) A' hn'
      ((map_mono hAN).trans (A.le_normalizer_map e.toMonoidHom))
  have hle : A' ≤ alternatingGroup (Fin 5) := by
    have he : A' ⊓ alternatingGroup (Fin 5) = A' := eq_of_le_of_card_ge inf_le_left (by
      rw [hA'c]
      exact (A' ⊓ alternatingGroup (Fin 5)).one_lt_card_iff_ne_bot.mpr hmeet)
    exact he.symm ▸ inf_le_right
  refine ⟨hAc,?_⟩
  apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
  rw [map_solvableResidual_eq _ e.surjective,
    WreathComponents.symmetric_residual]
  exact hle
end Theory.SpecificGroups.SymmetricFive
