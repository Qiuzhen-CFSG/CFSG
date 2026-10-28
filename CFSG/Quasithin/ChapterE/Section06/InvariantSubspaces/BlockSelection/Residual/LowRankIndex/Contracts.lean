module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Residual.IndexContracts

/-!
# Remaining A₃ inputs for the low-rank index argument

The perfect-quotient cases follow from cyclic Sylow transfer. The A₃ case
instead uses its binary module of order four, whose automorphism group has
order six. That intrinsic calculation is separated from normalization:
C.1.9 makes distinct conjugate blocks commute, and two such conjugates
would contradict three-rank at most one.

These are explicit pending proof obligations, not assertions of either
C.1.9 or the A₃ index calculation. The first retains characteristic two,
which discharges the extra O₂,₃ condition in C.1.9. The second requires
only relative normality and the actual A₃ block model, not an A₄ tag or
an assumed Sylow containment.

Source: Aschbacher–Smith, C.1.9 and C.1.12–13, printed pp.123–125, and
the proof of E.6.14, printed p.251 (PDF p.262).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection

/-- The A₃ specialization of C.1.9 for arbitrary conjugating elements in H.
An order-three-only specialization would not control higher three-power roots. -/
def AlternatingThreeConjugateCommutationInput (G : Type*) [Group G] : Prop :=
  ∀ H L : Subgroup G, HasCharacteristicTwo H → L ≤ H →
    ChapterC.IsAlternatingBlock L 3 → (L.subgroupOf H).IsSubnormal →
    ∀ x ∈ H, L.map (MulAut.conj x) ≠ L →
      L.map (MulAut.conj x) ≤ centralizer (L : Set G)

/-- The intrinsic A₃ index calculation after relative normality has been proved.
The bound applies to the whole ambient subgroup H, not just its selected block. -/
def AlternatingThreeNormalIndexInput (G : Type*) [Group G] : Prop :=
  ∀ H L : Subgroup G, L ≤ H → ChapterC.IsAlternatingBlock L 3 →
    (L.subgroupOf H).Normal → primeRank 3 H ≤ 1 → Nat.Coprime 3 (L.relIndex H)

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
