module

public import Theory.Representation.NormalInvariants
public import Theory.Representation.SubrepresentationLattice
public import Mathlib.RepresentationTheory.Character
public import Mathlib.Data.Complex.Basic

/-!
# Normal-subgroup norms and characteristic-two kernels

On an irreducible representation, the norm over a finite normal subgroup is
zero unless that subgroup acts trivially. Indeed, the norm takes values in
the subgroup's fixed space, which is either zero or the whole representation.
Taking traces gives the corresponding vanishing character sum over the subgroup.

A central involution acts trivially on every irreducible representation in
characteristic two. Starting with a nonzero vector, either it is fixed already
or its difference with its image is a nonzero fixed vector. The fixed space of
the central cyclic subgroup is therefore nonzero, and irreducibility makes
that subgroup act trivially. This argument needs no dimension hypothesis.

These are the kernel facts used in the principal-block argument for Z-star,
including the cyclic order-two case of Feit III.2.13(i). They are ported from
`Submission/ZStar/ModularKernel.lean` at historical commit `c3503435`.
The involution hypothesis is written explicitly as nonidentity and square one,
so this reusable module has no dependency on a campaign's involution definition.
-/

namespace ModularBlock.ModularKernel

open Representation
attribute [local instance] Fintype.ofFinite

/-- The norm over a finite normal subgroup of an irreducible representation
vanishes unless that subgroup acts trivially. -/
public theorem normalSubgroup_norm_eq_zero_or_le_ker
    {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]
    (rho : Representation F G V) [Representation.IsIrreducible rho]
    (H : Subgroup G) [Finite H] [H.Normal] :
    Representation.norm (rho.comp H.subtype) = 0 ∨ H ≤ rho.ker := by
  by_cases hfix : Representation.invariants (rho.comp H.subtype) = ⊥
  · left
    ext v
    have hv : Representation.norm (rho.comp H.subtype) v ∈
        Representation.invariants (rho.comp H.subtype) := by
      rw [Representation.mem_invariants]
      exact fun h => Representation.self_norm_apply (rho.comp H.subtype) h v
    simpa [hfix] using hv
  · exact Or.inr (le_ker_of_normal_invariants_ne_bot rho H hfix)

/-- A zero subgroup norm yields a zero character sum over that subgroup. -/
public theorem sum_character_eq_zero_of_normalSubgroup_norm_eq_zero
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) (H : Subgroup G) [Finite H]
    (hnorm : Representation.norm (rho.comp H.subtype) = 0) :
    ∑ h : H, rho.character (h : G) = 0 := by
  have htrace := congrArg (LinearMap.trace ℂ V) hnorm
  simpa [Representation.norm, Representation.character, map_sum] using htrace

/-- A central involution lies in the kernel of every irreducible
representation over a field of characteristic two. -/
public theorem central_involution_mem_ker_of_charTwo
    {F G V : Type*} [Field F] [CharP F 2] [Group G] [AddCommGroup V] [Module F V]
    (rho : Representation F G V) [Representation.IsIrreducible rho]
    {z : G} (hzI : z ≠ 1 ∧ z ^ 2 = 1) (hzCentral : z ∈ Subgroup.center G) :
    z ∈ rho.ker := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial rho
  let H := Subgroup.zpowers z
  have hHCenter : H ≤ Subgroup.center G := Subgroup.zpowers_le.mpr hzCentral
  have : H.Normal := by
    constructor
    intro h hh g
    have hhCenter : h ∈ Subgroup.center G := hHCenter hh
    simpa [Subgroup.mem_center_iff.mp hhCenter g]
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hfixed : ∃ w : V, w ≠ 0 ∧ rho z w = w := by
    by_cases hvFixed : rho z v = v
    · exact ⟨v, hv, hvFixed⟩
    · refine ⟨rho z v - v, sub_ne_zero.mpr hvFixed, ?_⟩
      have hzz : z * z = 1 := by simpa [pow_two] using hzI.2
      have hneg (x : V) : -x = x := by
        rw [neg_eq_iff_add_eq_zero]
        calc
          x + x = (2 : F) • x := (two_smul F x).symm
          _ = 0 := by
            have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
            rw [htwo, zero_smul]
      calc
        rho z (rho z v - v) = (rho z * rho z) v - rho z v := by rw [map_sub]; rfl
        _ = rho (z * z) v - rho z v := by rw [rho.map_mul]
        _ = v - rho z v := by rw [hzz]; simp
        _ = rho z v - v := by simp only [sub_eq_add_neg, hneg, add_comm]
  obtain ⟨w, hw, hzw⟩ := hfixed
  have hwInv : w ∈ Representation.invariants (rho.comp H.subtype) := by
    let zH : H := ⟨z, Subgroup.mem_zpowers z⟩
    have hgen : ∀ h : H, h ∈ Subgroup.zpowers zH := by
      intro h
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h.2
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext hn⟩
    exact (Representation.mem_invariants_iff_of_forall_mem_zpowers
      (rho.comp H.subtype) zH hgen w).mpr hzw
  have hInvNe : Representation.invariants (rho.comp H.subtype) ≠ ⊥ := by
    intro hbot
    exact hw (by simpa [hbot] using hwInv)
  exact le_ker_of_normal_invariants_ne_bot rho H hInvNe (Subgroup.mem_zpowers z)

end ModularBlock.ModularKernel
