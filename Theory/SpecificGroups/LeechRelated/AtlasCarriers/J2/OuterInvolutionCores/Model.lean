module

public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder
public import Theory.GroupTheory.SolvableResidual.Transport

/-!
# The perfect residual in the outer J₂ fixed-group model

The perfect residual of Aut(PSL₃(2)) is its actual inner automorphism subgroup:
that subgroup is perfect, and its quotient has order two. Its centralizer is
trivial because PSL₃(2) is centerless. We transport both conclusions through
an arbitrary actual fixed-group equivalence. The simple group of order 168
also has trivial three-core.

These calculations feed `J2.OuterInvolutionCores`, which still requires the
concrete representative's fixed-group identification. They do not establish
that identification. Source: GLS3, Table 5.3g, class 2C; Aschbacher--Smith,
proof of 15.3.38, printed p.1137. The imported exceptional isomorphism retains
its ATLAS attribution and license.
-/

public section
open Subgroup Theory.GroupTheory
namespace Sporadic.LeechRelated.J2.OuterInvolutionCores.Model
open Matrix.PSL3Two
local instance : Group.IsPerfect PSL := Atlas.psl_perfect 3 (by decide)
local instance : IsSimpleGroup PSL := Atlas.Comparisons.Exceptional.psl3Two_simple
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- Faithful inner conjugation of the actual projective matrix group. -/
noncomputable def innerEquiv : PSL ≃* MulAut.innerSubgroup PSL :=
  MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot
    Automorphisms.center_psl_eq_bot)

/-- The terminal derived subgroup is exactly the inner automorphism subgroup. -/
theorem residual_aut_eq_inner : solvableResidual (MulAut PSL) = MulAut.innerSubgroup PSL := by
  have hp : IsPGroup 2 (MulAut.Outer PSL) :=
    Automorphisms.outer_sl_isTwoGroup.of_equiv (MulAut.outerCongr Matrix.PSL3Two.equiv)
  let := hp.isNilpotent
  let : Group.IsPerfect (MulAut.innerSubgroup PSL) :=
    Group.IsPerfect.ofSurjective innerEquiv.surjective
  exact le_antisymm (solvableResidual_le_of_solvable_quotient _)
    (le_solvableResidual_of_isPerfect _)

/-- The residual has trivial centralizer in the full model automorphism group. -/
theorem centralizer_residual_aut :
    centralizer (solvableResidual (MulAut PSL) : Set (MulAut PSL)) = ⊥ := by
  rw [residual_aut_eq_inner]
  exact MulAut.centralizer_innerSubgroup_eq_bot Automorphisms.center_psl_eq_bot

/-- Restriction of a genuine fixed-group equivalence to its perfect residual. -/
noncomputable def residualEquiv {F : Type*} [Group F] [Finite F]
    (e : F ≃* MulAut PSL) : solvableResidual F ≃* PSL :=
  (e.solvableResidualEquiv.trans (MulEquiv.subgroupCongr residual_aut_eq_inner)).trans
    innerEquiv.symm

/-- The residual centralizer transports with the entire fixed-group model. -/
theorem centralizer_residual {F : Type*} [Group F] [Finite F]
    (e : F ≃* MulAut PSL) : centralizer (solvableResidual F : Set F) = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  apply mem_bot.mpr
  apply e.injective
  rw [map_one]
  apply mem_bot.mp
  rw [← centralizer_residual_aut]
  intro y hy
  rw [← map_solvableResidual_eq e.toMonoidHom e.surjective] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  change e z * e x = e x * e z
  simpa only [map_mul] using congrArg e (hx z hz)

/-- Simplicity and the order 168 exclude a nontrivial normal three-subgroup. -/
theorem threeCore_psl_eq_bot : pCore 3 PSL = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pCore 3 PSL) inferInstance with h | h
  · exact h
  · have hp : IsPGroup 3 PSL := by
      have ht : IsPGroup 3 (⊤ : Subgroup PSL) := h ▸ pCore_isPGroup
      exact ht.of_equiv topEquiv
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    have hc : Nat.Coprime 2 (Nat.card PSL) := hn ▸ (by decide : Nat.Coprime 2 3).pow_right n
    rw [card_PSL] at hc
    norm_num at hc

end Sporadic.LeechRelated.J2.OuterInvolutionCores.Model
