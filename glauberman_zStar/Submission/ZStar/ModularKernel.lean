import Submission.FeitThompson.Representation.SolvableDimension
import Submission.ZStar.LocalReduction

/-!
# Elementary characteristic-two kernel facts

This file records the part of Feit III.2.13 needed by the local principal-block
argument.  A central involution has a nonzero fixed vector in characteristic
two; irreducibility then forces it to act trivially.
-/

namespace Submission.ZStar

universe u v w

attribute [local instance] Fintype.ofFinite

/-- For an irreducible representation, the norm over a normal subgroup is
either zero or that subgroup acts trivially.  This is the ordinary
representation-theoretic dichotomy used to detect the kernel of the principal
congruence block. -/
theorem normalSubgroup_norm_eq_zero_or_le_ker
    {F : Type u} [Field F]
    {G : Type v} [Group G]
    {V : Type w} [AddCommGroup V] [Module F V]
    (rho : Representation F G V) [Representation.IsIrreducible rho]
    (H : Subgroup G) [Finite H] [H.Normal] :
    Representation.norm (rho.comp H.subtype) = 0 ∨ H ≤ rho.ker := by
  letI : Nontrivial V :=
    Subrepresentation.irreducible_module_nontrivial rho
  let S : Subrepresentation rho := fixedSubrepresentationOfNormal rho H
  rcases (inferInstance : Representation.IsIrreducible rho).eq_bot_or_eq_top S with
    hSbot | hStop
  · left
    ext x
    have hxInv : Representation.norm (rho.comp H.subtype) x ∈
        Representation.invariants (rho.comp H.subtype) := by
      rw [Representation.mem_invariants]
      intro h
      exact Representation.self_norm_apply (rho.comp H.subtype) h x
    have hxBot : Representation.norm (rho.comp H.subtype) x ∈
        (⊥ : Submodule F V) := by
      have hInvBot : Representation.invariants (rho.comp H.subtype) =
          (⊥ : Submodule F V) := by
        calc
          Representation.invariants (rho.comp H.subtype) = S.toSubmodule := rfl
          _ = (⊥ : Subrepresentation rho).toSubmodule :=
            congrArg Subrepresentation.toSubmodule hSbot
          _ = (⊥ : Submodule F V) := rfl
      rw [hInvBot] at hxInv
      exact hxInv
    simpa using hxBot
  · right
    apply le_ker_of_normal_invariants_ne_bot rho H
    intro hInvBot
    have hSbot : S = ⊥ := by
      apply Subrepresentation.toSubmodule_injective
      calc
        S.toSubmodule = Representation.invariants (rho.comp H.subtype) := rfl
        _ = (⊥ : Submodule F V) := hInvBot
        _ = (⊥ : Subrepresentation rho).toSubmodule := rfl
    exact (show S ≠ ⊥ by rw [hStop]; exact top_ne_bot) hSbot

/-- If the norm of a restricted complex representation is zero, then the sum
of its character over that subgroup is zero. -/
theorem sum_character_eq_zero_of_normalSubgroup_norm_eq_zero
    {G : Type v} [Group G]
    {V : Type w} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) (H : Subgroup G) [Finite H]
    (hnorm : Representation.norm (rho.comp H.subtype) = 0) :
    ∑ h : H, rho.character (h : G) = 0 := by
  have htrace := congrArg (LinearMap.trace ℂ V) hnorm
  simpa [Representation.norm, Representation.character, map_sum] using htrace

/-- A central involution acts trivially on every irreducible representation in
characteristic two.  This is the cyclic order-two case of Feit III.2.13(i). -/
theorem central_involution_mem_ker_of_charTwo
    {F : Type u} [Field F] [CharP F 2]
    {G : Type v} [Group G]
    {V : Type w} [AddCommGroup V] [Module F V]
    (rho : Representation F G V) [Representation.IsIrreducible rho]
    {z : G} (hzI : IsInvolution z)
    (hzCentral : z ∈ Subgroup.center G) :
    z ∈ rho.ker := by
  letI : Nontrivial V :=
    Subrepresentation.irreducible_module_nontrivial rho
  let H : Subgroup G := Subgroup.zpowers z
  have hHCenter : H ≤ Subgroup.center G := by
    exact Subgroup.zpowers_le.mpr hzCentral
  have hHNormal : H.Normal := by
    constructor
    intro h hh g
    have hhCenter : h ∈ Subgroup.center G := hHCenter hh
    simpa [Subgroup.mem_center_iff.mp hhCenter g]
  letI : H.Normal := hHNormal
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hfixed : ∃ w : V, w ≠ 0 ∧ rho z w = w := by
    by_cases hvFixed : rho z v = v
    · exact ⟨v, hv, hvFixed⟩
    · let w : V := rho z v - v
      have hw : w ≠ 0 := sub_ne_zero.mpr hvFixed
      refine ⟨w, hw, ?_⟩
      have hzz : z * z = 1 := by
        simpa [pow_two] using hzI.2
      calc
        rho z w = rho z (rho z v - v) := rfl
        _ = rho z (rho z v) - rho z v := by rw [map_sub]
        _ = (rho z * rho z) v - rho z v := rfl
        _ = rho (z * z) v - rho z v := by rw [rho.map_mul]
        _ = v - rho z v := by rw [hzz]; simp
        _ = rho z v - v := by
          have hneg : ∀ x : V, -x = x := by
            intro x
            rw [neg_eq_iff_add_eq_zero]
            calc
              x + x = (2 : F) • x := (two_smul F x).symm
              _ = 0 := by
                have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
                rw [htwo, zero_smul]
          simp only [sub_eq_add_neg, hneg, add_comm]
        _ = w := rfl
  obtain ⟨w, hw, hzw⟩ := hfixed
  have hwInv : w ∈ Representation.invariants (rho.comp H.subtype) := by
    let zH : H := ⟨z, Subgroup.mem_zpowers z⟩
    have hgen : ∀ h : H, h ∈ Subgroup.zpowers zH := by
      intro h
      rcases Subgroup.mem_zpowers_iff.mp h.2 with ⟨n, hn⟩
      apply Subgroup.mem_zpowers_iff.mpr
      refine ⟨n, ?_⟩
      exact Subtype.ext hn
    apply (Representation.mem_invariants_iff_of_forall_mem_zpowers
      (rho.comp H.subtype) zH hgen w).mpr
    exact hzw
  have hInvNe : Representation.invariants (rho.comp H.subtype) ≠ ⊥ := by
    intro hbot
    have : w = 0 := by
      simpa [hbot] using hwInv
    exact hw this
  exact le_ker_of_normal_invariants_ne_bot rho H hInvNe
    (Subgroup.mem_zpowers z)

end Submission.ZStar
