module

public import Stellmacher.Recognition.LargeTerminalReeCentralizer
public import Theory.GroupTheory.Recognition.ReeTwo.CentralizerExclusion

/-!
# Excluding the order-4096 large-terminal endpoint

At the upper large-terminal endpoint, the actual involution centralizer is
identified with the verified q = 2 Ree centralizer.  The simple-group
exclusion for that centralizer then rules out the endpoint.  This wrapper
keeps the original `LargeTerminalContext` hypotheses and performs no
recognition from cardinalities alone.

Source: Shinoda (1975), pp.79 and 85, with the local identification from
Thompson VI, pp.629--630 and its formal root-relations development.
-/

namespace Stellmacher.Recognition

universe u

/-- A finite nonsolvable simple group cannot realize the order-4096
large-terminal endpoint. -/
public theorem LargeTerminalContext.false_of_sylow_card_eq_4096
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    {S0 : Sylow 2 G} (ctx : LargeTerminalContext S0)
    (hns : ¬ Group.IsSolvable G) (hS : Nat.card S0 = 4096) :
    False := by
  obtain ⟨z, hz, _hgen, hcentral, _hodd, ⟨ec, _hzroot, _hcore⟩⟩ :=
    ctx.exists_ree_centralizer_of_large_card hS
  exact ReeTwo.false_of_centralizer_equiv hns S0 z hz hcentral ec.symm

end Stellmacher.Recognition
