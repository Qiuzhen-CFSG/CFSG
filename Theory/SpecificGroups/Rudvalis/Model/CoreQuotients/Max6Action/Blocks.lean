module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Cardinality.Max6Comparison
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Five invariant blocks for the sixth Rudvalis ATLAS word subgroup

The two original max6 generators permute the five displayed 16-point subsets
of the degree-4060 carrier. We check only these block images against the cached
permutations, whose comparison with the original words is proved upstream.
The induced permutations are an inverse five-cycle and an adjacent swap, which
generate the whole symmetric group.

The block witnesses were discovered with GAP (`source/DiscoverBlocks.g`);
every fact used here is checked by the Lean kernel.
The ATLAS data attribution is in `SylowOvergroups.Definitions`.
Source: GLS3 Table 5.3r, printed p.279; this supplies the S₅ quotient needed
in the Rudvalis case of Aschbacher–Smith E.1.14(5), printed p.214.
-/

namespace Rudvalis.CoreQuotients.Max6Blocks
open SylowOvergroups
open SylowOvergroups.LocalCardinality.Max6

@[expose] public def block : Fin 5 → Finset (Fin 4060)
  | 0 => {66, 384, 494, 734, 1057, 1071, 1139, 1714, 1841, 2191, 2598, 2808, 2991, 3190, 3448, 3714}
  | 1 => {407, 492, 826, 964, 1064, 1068, 1140, 1231, 1246, 1337, 1691, 1851, 1970, 2151, 3607, 3633}
  | 2 => {74, 99, 184, 370, 372, 520, 620, 808, 1230, 1795, 2109, 2115, 2315, 2354, 3440, 3610}
  | 3 => {531, 847, 1030, 1267, 1451, 1628, 1633, 1903, 1905, 2314, 2322, 2535, 3141, 3368, 3781, 3828}
  | _ => {421, 527, 776, 861, 944, 1086, 1945, 2009, 2092, 2499, 2521, 2791, 3531, 3641, 3762, 3992}

@[expose] public def cycle : Equiv.Perm (Fin 5) := (finRotate 5)⁻¹

@[expose] public def transposition : Equiv.Perm (Fin 5) := Equiv.swap 2 3

public theorem block_injective : Function.Injective block := by
  intro i j
  revert i j
  decide +kernel

public theorem gen0_block (i : Fin 5) :
    (block i).map (L0.gen 0).toEmbedding = block (cycle i) := by
  revert i
  decide +kernel

public theorem gen1_block (i : Fin 5) :
    (block i).map (L0.gen 1).toEmbedding = block (transposition i) := by
  revert i
  decide +kernel

/-- Each block has sixteen points of the unchanged carrier. -/
public theorem block_card (i : Fin 5) : (block i).card = 16 := by
  revert i
  decide +kernel

/-- The two certified block permutations generate S₅. -/
public theorem cycle_transposition_generate :
    Subgroup.closure ({cycle, transposition} : Set (Equiv.Perm (Fin 5))) = ⊤ := by
  have hswap : transposition = Equiv.swap 3 (cycle 3) := by decide +kernel
  rw [hswap]
  exact Equiv.Perm.closure_cycle_adjacent_swap
    (Equiv.Perm.IsCycle.inv isCycle_finRotate) (by simp) 3

end Rudvalis.CoreQuotients.Max6Blocks
