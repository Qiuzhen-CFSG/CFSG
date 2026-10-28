module
public import Theory.Representation.PSL3Two.NaturalDualNonFF
public import Theory.Representation.BinaryOffender.Embedding

/-!
# A marked natural--dual submodule controls the whole actor

A faithful action on the component and an equivariant embedding of its
natural--dual module rule out FF offenders on the ambient module. The same
embedding transfers the quadratic budget, forcing a quadratic actor to induce
inner automorphisms. The ambient fixed summand need not be marked or split.

Source: Aschbacher--Smith, 14.6.24(a)--(b) and (4), pp.1039--1041.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace BinaryLinearThree.NaturalDual
variable {H E : Type*} [_root_.Group H] [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]
    (ρ : Representation (ZMod 2) H E) (ι : H →* MulAut Group)
    (hι : Function.Injective ι) (e : Space →ₗ[ZMod 2] E) (he : Function.Injective e)
    (hact : ∀ g v, ρ g (e v) = e (autAction (ι g) v))

include hι e he hact in
/-- A faithful component action and the literal pair submodule exclude every
offender, even when the ambient module has additional fixed vectors. -/
theorem not_ff_of_pair_embedding : ¬ IsFFModule ρ := by
  rintro ⟨A,hA⟩
  exact not_isFFModule_autAction
    ⟨A.map ι, hA.map_of_embedding ρ autAction ι e he hact hι⟩

include hι in
/-- The component automorphism action bounds the full actor's two-rank. -/
theorem two_rank_le_of_component_embedding [Finite H] : primeRank 2 H ≤ 2 := by
  apply (primeRank_le_of_injective 2 ι hι).trans
  rw [primeRank_equiv 2 (MulAut.congr Matrix.PSL3Two.equiv)]
  exact (Matrix.PSL3Even.automorphism_two_rank_eq_of_card_two (ZMod 2)
    (by simp)).le

include hι e he hact in
/-- The actual quadratic inequality forces support preservation through
innerness; it is not assumed from quadraticity alone. -/
theorem inner_of_pair_embedding (A : Subgroup H) (hA : IsElementaryTwo A)
    (hq : IsQuadratic ρ A) (hbudget : fixedCodim ρ A ≤ 2 * rank A) :
    A.map ι ≤ MulAut.innerSubgroup Group := by
  let : IsElementaryAbelian 2 A := hA.2
  have hAi : IsElementaryTwo (A.map ι) :=
    ⟨fun hz => hA.1 ((Subgroup.map_eq_bot_iff_of_injective A hι).mp hz),
      IsElementaryAbelian.map ι⟩
  have hqi : IsQuadratic autAction (A.map ι) := by
    rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ v
    apply he
    have hh := hq a ha b hb (e v)
    simpa only [hact, ← map_sub] using hh
  apply LowRankProfiles.inner_of_quadratic_budget autAction autAction_inner _ hAi hqi
  rw [rank_map_injective ι hι]
  exact (fixedCodim_map_le_of_embedding ρ autAction ι e he hact A).trans hbudget

end BinaryLinearThree.NaturalDual
