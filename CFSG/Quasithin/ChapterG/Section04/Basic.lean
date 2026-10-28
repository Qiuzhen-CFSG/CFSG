module

public import CFSG.Quasithin.ChapterG.Section04.Defs

/-!
# The two-core reduction in G.4

Lemma G.4.3 is independent of the later McLaughlin recognition.  It is the
standard modular fixed-point argument: a normal two-subgroup has a nonzero
fixed point, irreducibility makes the fixed space all of `V`, and faithfulness
of the literal additive action forces the subgroup to be trivial.

The remaining assertions of G.4.1 require the symplectic transvection geometry
and the finite list of component actions.  They are intentionally kept out of
this elementary module; the source assembly will discharge those obligations.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterG.Section04

open Subgroup

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  [Finite V] [Nontrivial V]

/-- The binary-action form of Lemma G.4.3 for the actual action image `G₀`.

The `Setup` field `irreducible` records the explicit binary bridge needed by
the fixed-point lemma; it is not inferred from an unformalized `F`-linear
claim.
-/
theorem lemma_G_4_3 (S : Setup (F := F) (V := V)) :
    pCore 2 S.G₀ = ⊥ := by
  let _ := S.binary_elementary
  exact irreducible_range_two_core_eq_bot S.G₀ S.irreducible

omit [Finite V] [Nontrivial V] in
/- The generated transvection subgroup is a genuine subgroup of the source
ambient action image. -/
theorem generated_le_G₀ (S : Setup (F := F) (V := V)) :
    S.generated ≤ S.G₀ :=
  S.generated_le

omit [Finite V] [Nontrivial V] in
/- Conjugation stability of the marked transvections makes the generated group
normal in the source action image. -/
theorem generated_normal (S : Setup (F := F) (V := V)) :
    (S.generated.subgroupOf S.G₀).Normal :=
  S.generated_normal

omit [Finite V] [Nontrivial V] in
/- The marked transvection set generates a nontrivial subgroup. -/
theorem generated_ne_bot (S : Setup (F := F) (V := V)) :
    S.generated ≠ ⊥ :=
  S.generated_ne_bot

end CFSG.Quasithin.ChapterG.Section04

