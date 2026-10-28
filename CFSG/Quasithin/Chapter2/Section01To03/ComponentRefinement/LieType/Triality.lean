module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Setup
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Blocks
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.BlockObstructions
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Triality.ParabolicTransport
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Triality.BlockNumerics
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Triality.RelativeOvergroups
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Triality.ShortSubgroups

/-!
# Triality exclusion for the component refinement

Aligning an actual model equivalence with S ∩ L gives two N_S(L)-invariant
root parabolics. Their joins with all of S belong to HeOver and together
generate ⟨L,S⟩. Since L is outside M, the local block decomposition forces
an escaping χ₀ block in one of these overgroups. The relative short-subgroup
calculation excludes it: the genuine radical actions kill every coordinate
of a short subnormal subgroup in the component orbit, and its remaining
two-group kernel is incompatible with two-perfection and a nonzero module.

The local Levi quotients are PSL₂(q³) and PSL₂(q), respectively, with the
full parabolics kept distinct from their local factors. The root-action
obstruction includes q = 2 and its order-three actors. All model geometry
and short-subgroup premises are discharged in `not_standard`.

Source: Aschbacher–Smith 1.1.5(3)(a) and 2.3.9(7), printed pp.501 and 526.
The source's literal inner action is accepted by `not_standard_of_inner_action`;
the stronger geometric argument does not need it. No assumption that S
normalizes L is made. `not_isTrialityGroupAt_two_pow` applies the exclusion
directly to the genuine model predicate used by Theorem C's triality branch.
-/

public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.TrialityCase

open Subgroup
open _root_.Triality.Standard

variable {G : Type*} [Group G]

/-- Conditional generation reduction. The geometric premises concern the
actual finite root candidates and their joins with S. The escaping subgroup
is a block relative to that join, rather than to the ambient group G. -/
theorem exists_escaping_parabolic_block {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) {P : Parameters} (e : L ≃* Carrier P)
    (hgen : Parabolics.parabolic P .arms ⊔ Parabolics.parabolic P .central = ⊤)
    (he : ∀ a, parabolicOvergroup e ((S : Subgroup H).map H.subtype) a ∈
      Chapter1.He G) :
    (∃ B : Subgroup (parabolicOvergroup e ((S : Subgroup H).map H.subtype) .arms),
      EscapingBlock M ((S : Subgroup H).map H.subtype)
        (parabolicOvergroup e ((S : Subgroup H).map H.subtype) .arms) B) ∨
    (∃ B : Subgroup (parabolicOvergroup e ((S : Subgroup H).map H.subtype) .central),
      EscapingBlock M ((S : Subgroup H).map H.subtype)
        (parabolicOvergroup e ((S : Subgroup H).map H.subtype) .central) B) := by
  apply exists_escapingBlock_of_pair h.blocks h.outside
  · rw [parabolicOvergroup_sup e _ hgen]
    exact le_sup_left
  · exact parabolicOvergroup_le e _ .arms
  · exact parabolicOvergroup_le e _ .central
  · exact parabolicOvergroup_mem_HeOver h e .arms (he .arms)
  · exact parabolicOvergroup_mem_HeOver h e .central (he .central)

/-- The genuine triality component is incompatible with the local block
constraints of 2.3.9(7). The invariant parabolics, their generation, their
HeOver membership and both relative block obstructions are all constructed.
The positive exponent is part of `Parameters`; in particular q = 2 is included. -/
theorem not_standard {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) {P : Parameters} (hp : P.prime = 2)
    (e₀ : L ≃* Carrier P) : False := by
  obtain ⟨e, _, hinv, he, _⟩ := exists_relative_overgroups h hp e₀
  obtain ⟨ho₁, ho₂⟩ := parabolicOvergroup_blockObstructions h hp e hinv
  rcases exists_escaping_parabolic_block h e (Parabolics.parabolic_sup_binary P hp) he with
    ⟨B, ha, hm, hc⟩ | ⟨B, ha, hm, hc⟩
  · exact hm (ho₁ B ha hc)
  · exact hm (ho₂ B ha hc)

/-- Apply the exclusion to exactly the genuine model and literal inner action
supplied by 1.1.5(3)(a). The stronger theorem above makes the action unnecessary. -/
theorem not_standard_of_inner_action {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) {P : Parameters} (hp : P.prime = 2)
    (e : L ≃* Carrier P) (α : MulAut L)
    (_hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (_hinner : α ∈ (MulAut.conj (G := L)).range) : False :=
  not_standard h hp e

/-- Discharge the actual triality model predicate in Theorem C's
characteristic-two list. Its field order forces the defining prime to be two. -/
theorem not_isTrialityGroupAt_two_pow {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (n : ℕ) : ¬ IsTrialityGroupAt (2 ^ n) L := by
  rintro ⟨P, hq, ⟨e⟩⟩
  have hp : P.prime = 2 := by
    apply (Nat.prime_dvd_prime_iff_eq P.prime_prime Nat.prime_two).mp
    apply P.prime_prime.dvd_of_dvd_pow
    rw [← hq]
    exact dvd_pow_self P.prime (Nat.ne_of_gt P.exponent_pos)
  exact not_standard h hp e

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.TrialityCase

end
