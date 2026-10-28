module

public import Theory.Representation.BinaryOddDisplacement.PrimeDivisibility

/-!
# Fixed ranks of endomorphisms commuting with a binary five-group

If a five-group has zero fixed space, every invariant subspace has binary
dimension divisible by four. In particular this applies to the fixed space
of a commuting linear endomorphism. The proof restricts the action to that
kernel and uses the multiplicative order of two modulo five. Thus a
commuting endomorphism cannot have fixed rank six. No semisimplicity or
assumed decomposition into rank-four constituents is needed.

Source application: the final contradiction in Aschbacher–Smith 8.2.8(6),
printed p.719, via `TensorRecognition.CodeObstruction`.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace Representation
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The commuting fixed space has rank divisible by four. -/
theorem four_dvd_fixedRank_of_commuting_five
    (ρ : Representation (ZMod 2) D V) (hD : IsPGroup 5 D)
    (hfix : ρ.invariants = ⊥) (t : V →ₗ[ZMod 2] V)
    (hc : ∀ d v, t (ρ d v) = ρ d (t v)) :
    4 ∣ Module.finrank (ZMod 2) (LinearMap.ker (t - LinearMap.id)) := by
  let S : Subrepresentation ρ := {
    toSubmodule := (t - LinearMap.id).ker
    apply_mem_toSubmodule := by
      intro d v hv
      change t (ρ d v) - ρ d v = 0
      have hv' : t v = v := sub_eq_zero.mp hv
      rw [hc, hv', sub_self] }
  have hz : S.toRepresentation.invariants = ⊥ := by
    apply bot_unique
    intro v hv
    have hh : (v : V) ∈ ρ.invariants := by
      intro d
      exact congrArg Subtype.val (hv d)
    rw [hfix] at hh
    exact Subtype.ext hh
  exact (show orderOf (2 : ZMod 5) = 4 from BinaryPrimeDegree.orderOf_two_mod_five) ▸
    orderOf_two_dvd_finrank_of_isPGroup S.toRepresentation (by decide) (by decide) hD hz

/-- A fixed rank of six contradicts the fixed-point-free five-group action. -/
theorem no_six_fixedRank_of_commuting_five
    (ρ : Representation (ZMod 2) D V) (hD : IsPGroup 5 D)
    (hfix : ρ.invariants = ⊥) (t : V →ₗ[ZMod 2] V)
    (hc : ∀ d v, t (ρ d v) = ρ d (t v)) :
    Module.finrank (ZMod 2) (LinearMap.ker (t - LinearMap.id)) ≠ 6 := by
  intro hd
  have hh := four_dvd_fixedRank_of_commuting_five ρ hD hfix t hc
  rw [hd] at hh
  norm_num at hh

end Representation
