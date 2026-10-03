module
public import Stellmacher.Recognition.TerminalReduction
public import Stellmacher.Recognition.SemidihedralSylowSixteen
public import Stellmacher.Recognition.GTwoSylow
public import Stellmacher.SectionTen.TenOneLargeSylowBounds

/-!
# The remaining Sylow orders in the simple N2 classification

A finite nonsolvable simple N2 group with trivial odd cores in every
two-local subgroup, and not already in the actual isomorphism catalogue,
has Sylow two-subgroup order 16, 32, 64, 2048, or 4096. The unconditional
corollary keeps the recognized-model and bad-odd-core involution-centralizer
alternatives explicit. Neither theorem identifies groups by their order.

Apply the rich terminal reduction. The G2 local type gives orders 32 or 64,
the semidihedral GL2(3) centralizer model gives order 16, and the remaining
maximal C2 times S4 branch already has order 32. In the large terminal
branch the original graph Sylow is the restriction of the supplied ambient
Sylow. Transport its bounds 2^11 through 2^12 along that exact restriction
equivalence, then use the Sylow two-power order to obtain the two endpoints.
The bad odd-core branch contradicts the two-local odd-core hypothesis because
an involution centralizer is itself two-local.

This numerical reduction feeds the global recognition campaign without
changing the existing structural alternatives. Source: Stellmacher
Section 11, (8.6), and (10.1), together with the ABG characteristic-three
centralizer specialization and the exact sources of the imported results.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven
universe u

private theorem large_sylow_card
    {G : Type u} [Group G] [Finite G] {S0 : Sylow 2 G}
    (ctx : LargeTerminalContext S0) :
    Nat.card S0 = 2048 ∨ Nat.card S0 = 4096 := by
  let tenCtx := ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three
  let cp := ctx.terminal.criticalPath
  have hlength : cp.length = 3 := ctx.length_three
  let middle := cp.path ⟨2, by omega⟩
  have hpath : IsCriticalPathOffset ctx.terminal.Γ cp 2 middle :=
    ⟨⟨2, by omega⟩, rfl, rfl⟩
  have hcard : Nat.card ((S0 : Subgroup G).subgroupOf (ctx.first ⊔ ctx.second)) =
      Nat.card S0 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe ctx.terminal.sylow_le_join).toEquiv
  have hb := SectionTen.ten_one_large_sylow_card_bounds tenCtx middle hpath ctx.noTransvections
  change 2 ^ 11 ≤ Nat.card ((S0 : Subgroup G).subgroupOf (ctx.first ⊔ ctx.second)) ∧
    Nat.card ((S0 : Subgroup G).subgroupOf (ctx.first ⊔ ctx.second)) ≤ 2 ^ 12 at hb
  rw [hcard] at hb
  obtain ⟨n, hn⟩ := S0.isPGroup'.exists_card_eq
  rw [hn] at hb ⊢
  have hlo : 11 ≤ n := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb.1
  have hhi : n ≤ 12 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb.2
  have he : n = 11 ∨ n = 12 := by omega
  rcases he with rfl | rfl <;> norm_num

/-- The actual large terminal context restricts the supplied ambient Sylow
to the two proved endpoints, without any global recognition assumption. -/
public theorem LargeTerminalContext.sylow_card
    {G : Type u} [Group G] [Finite G] {S0 : Sylow 2 G}
    (ctx : LargeTerminalContext S0) :
    Nat.card S0 = 2048 ∨ Nat.card S0 = 4096 :=
  large_sylow_card ctx

public theorem simple_nTwo_sylow_spectrum
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G) (S0 : Sylow 2 G)
    (hcore : ∀ U : Subgroup G, IsTwoLocal U → pPrimeCore 2 U = ⊥)
    (hmodel : ¬ IsNTwoGroupModel G) :
    Nat.card S0 = 16 ∨ Nat.card S0 = 32 ∨ Nat.card S0 = 64 ∨
      Nat.card S0 = 2048 ∨ Nat.card S0 = 4096 := by
  rcases simple_nTwo_terminal_reduction hns hN S0 with hm | ⟨_, hlocal⟩ | hbad
  · exact (hmodel hm).elim
  · rcases hlocal with hG2 | hlarge | hsemi | ⟨h32, _⟩
    · rcases sylow_card_of_gTwoTwoDerived_type S0 hG2 with h32 | h64
      · exact Or.inr (Or.inl h32)
      · exact Or.inr (Or.inr (Or.inl h64))
    · obtain ⟨ctx⟩ := hlarge
      exact Or.inr (Or.inr (Or.inr (large_sylow_card ctx)))
    · exact Or.inl (semidihedral_sylow_card_of_simple_nTwo S0 hsemi hN hcore)
    · exact Or.inr (Or.inl h32)
  · obtain ⟨z, hz, hbad⟩ := hbad
    exact (hbad (hcore _ (Theory.GroupTheory.isTwoLocal_involution_centralizer hz))).elim

public theorem simple_nTwo_sylow_reduction
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G) (S0 : Sylow 2 G) :
    IsNTwoGroupModel G ∨
    (Nat.card S0 = 16 ∨ Nat.card S0 = 32 ∨ Nat.card S0 = 64 ∨
      Nat.card S0 = 2048 ∨ Nat.card S0 = 4096) ∨
    (∃ z : G, orderOf z = 2 ∧
      pPrimeCore 2 (Subgroup.centralizer ({z} : Set G)) ≠ ⊥) := by
  by_cases hmodel : IsNTwoGroupModel G
  · exact Or.inl hmodel
  rcases simple_nTwo_terminal_reduction hns hN S0 with hm | ⟨hcore, _⟩ | hbad
  · exact (hmodel hm).elim
  · exact Or.inr (Or.inl (simple_nTwo_sylow_spectrum hns hN S0 hcore hmodel))
  · exact Or.inr (Or.inr hbad)

end Stellmacher.Recognition
