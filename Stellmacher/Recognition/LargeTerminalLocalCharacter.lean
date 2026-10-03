module

public import Stellmacher.Recognition.LargeTerminalLocalCharacterData
public import Theory.GroupTheory.IndexEightCharacter

/-!
# A Sylow character detecting the proper residual extension

At Sylow order 4096, the first residual `R` and second local core `Q`
restrict to normal subgroups of the prescribed Sylow `S`, of orders 512
and 1024. The quotient `S / Q` is cyclic of order four, and a conjugate
of a terminal module involution lies in `S` outside `Q`. The index-eight
character-extension lemma therefore extends the nontrivial character of
`Q / R` to `S`. In particular, its kernel meets `Q` exactly in `R`.

The native subgroup facts come from Stellmacher (10.1)(b) and the terminal
module/core noncontainment preceding it; see
`refs/latex/stellmacher-n-group.tex` and `LargeTerminalLocalCharacterData`.
-/

namespace Stellmacher.Recognition

open SectionsFiveToSeven

universe u

/-- At the upper Sylow endpoint, a binary character detects precisely the
first residual among elements of the second local core. -/
public theorem LargeTerminalContext.exists_local_character
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096) :
    ∃ χ : S →* Multiplicative (ZMod 2),
      ∀ s : S, (s : G) ∈ twoCoreIn ctx.second →
        (χ s = 1 ↔ (s : G) ∈ ctx.firstResidual) := by
  let R := ctx.firstResidual.subgroupOf (S : Subgroup G)
  let Q := (twoCoreIn ctx.second).subgroupOf (S : Subgroup G)
  let : R.Normal := ctx.local_character_residual_normal
  let : Q.Normal := ctx.local_character_core_normal
  let : IsCyclic (S ⧸ Q) := ctx.local_character_quotient_cyclic
  have hR : Nat.card R = 512 := ctx.local_character_residual_card
  have hQ : Nat.card Q = 1024 := ctx.local_character_core_card hS
  exact exists_character_of_index_eight R Q ctx.local_character_residual_le_core
    (by omega) (by omega) ctx.local_character_escaping_involution

end Stellmacher.Recognition
