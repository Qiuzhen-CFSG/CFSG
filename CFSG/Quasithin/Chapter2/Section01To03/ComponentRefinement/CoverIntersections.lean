module

public import CFSG.Quasithin.Chapter1.Defs

/-!
# Intersections with odd central covers

An even-characteristic subgroup of a group with odd prime-power center
meets that center trivially. Indeed the intersection centralizes its two-core,
so is contained in that two-core, and coprime prime-power subgroups are disjoint.
Thus the subgroup embeds in the central quotient.

This is needed to read the stabilizer assertion for the triple cover of A₇
in Aschbacher–Smith 2.3.9(7)(c), printed p.525. A subgroup of characteristic
two cannot be the full inverse image of a quotient stabilizer when the center
has order three. The actual intersection is identified through its injective
map into the quotient. Establishing its image remains a model-local problem.
Notation A.3.5, printed p.43, specifies the covers by their quasisimplicity,
center of order three, and actual alternating central quotient.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement

open Subgroup

variable {K : Type*} [Group K]

/-- A characteristic-two subgroup meets a coprime prime-power center trivially. -/
theorem center_inf_eq_bot_of_even {N : Subgroup K} (hN : N ∈ Chapter1.He K)
    {p : ℕ} (hZ : IsPGroup p (center K)) (hp : Nat.Coprime p 2) :
    center K ⊓ N = ⊥ := by
  have hd := hZ.disjoint_of_coprime (isPGroup_pCoreIn 2 N) hp
  apply le_bot_iff.mp
  rintro x ⟨hxZ, hxN⟩
  have hxcore : x ∈ N.pCoreIn 2 := by
    apply hN
    refine ⟨hxN, mem_centralizer_iff.mpr ?_⟩
    intro y _
    exact mem_center_iff.mp hxZ y
  exact Subgroup.disjoint_def.mp hd hxZ hxcore

/-- The restriction of the central quotient map to this subgroup is injective. -/
theorem central_quotient_injective_of_even {N : Subgroup K}
    (hN : N ∈ Chapter1.He K) {p : ℕ}
    (hZ : IsPGroup p (center K)) (hp : Nat.Coprime p 2) :
    Function.Injective ((QuotientGroup.mk' (center K)).comp N.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro x hx
  have hxZ : (x : K) ∈ center K :=
    (QuotientGroup.eq_one_iff (x : K)).mp (MonoidHom.mem_ker.mp hx)
  have hm : (x : K) ∈ center K ⊓ N := ⟨hxZ, x.property⟩
  rw [center_inf_eq_bot_of_even hN hZ hp, mem_bot] at hm
  exact Subtype.ext hm

/-- The nonsplit threefold-cover case, with the source's actual center order. -/
theorem triple_cover_quotient_injective_of_even [Finite K] {N : Subgroup K}
    (hN : N ∈ Chapter1.He K) (hZ : Nat.card (center K) = 3) :
    Function.Injective ((QuotientGroup.mk' (center K)).comp N.subtype) := by
  have hp : IsPGroup 3 (center K) :=
    (IsPGroup.iff_card).mpr ⟨1, by simpa using hZ⟩
  exact central_quotient_injective_of_even hN hp (by decide)

end CFSG.Quasithin.Chapter2.ComponentRefinement

end
