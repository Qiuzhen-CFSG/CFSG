module

public import Stellmacher.Recognition.SylowSpectrum
public import Stellmacher.Recognition.LargeTerminalReeExclusion

/-!
# The Sylow order in the large terminal branch

The Section Ten bounds leave the two endpoints `2048` and `4096` for the
prescribed Sylow subgroup.  The accepted upper-endpoint exclusion identifies
the order-4096 centralizer with the verified q = 2 Ree centralizer and rules
that endpoint out in a finite nonsolvable simple group.  Hence every actual
large terminal context has Sylow order 2048.

Source: Stellmacher (10.1), Section 11, and the q = 2 Ree centralizer
exclusion from Shinoda (1975), pp. 79 and 85.
-/

namespace Stellmacher.Recognition

universe u

/-- The upper Sylow endpoint is impossible in a finite nonsolvable simple
large-terminal context. -/
public theorem LargeTerminalContext.sylow_card_eq_2048
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    {S : Sylow 2 G} (ctx : LargeTerminalContext S)
    (hns : ¬ Group.IsSolvable G) :
    Nat.card S = 2048 := by
  rcases ctx.sylow_card with h2048 | h4096
  · exact h2048
  · exact (ctx.false_of_sylow_card_eq_4096 hns h4096).elim

/-- The large branch of the simple N2 terminal reduction has Sylow order
2048.  The odd-core hypothesis is retained in the interface because it is the
branch invariant supplied by `simple_nTwo_terminal_reduction`. -/
public theorem simple_nTwo_large_terminal_sylow_card
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (S : Sylow 2 G)
    (hcore : ∀ U : Subgroup G, IsTwoLocal U → pPrimeCore 2 U = ⊥)
    (ctx : LargeTerminalContext S) :
    Nat.card S = 2048 := by
  have _hN := hN
  have _hcore := hcore
  exact ctx.sylow_card_eq_2048 hns

/-- Extract the large-terminal context from the terminal reduction and apply
the endpoint theorem. -/
public theorem simple_nTwo_large_terminal_branch_sylow_card
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (S : Sylow 2 G)
    (hcore : ∀ U : Subgroup G, IsTwoLocal U → pPrimeCore 2 U = ⊥)
    (hctx : Nonempty (LargeTerminalContext S)) :
    Nat.card S = 2048 := by
  obtain ⟨ctx⟩ := hctx
  exact simple_nTwo_large_terminal_sylow_card hns hN S hcore ctx

end Stellmacher.Recognition
