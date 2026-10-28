module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Residual.FaithfulIndex.Contracts

/-!
# The alternating-three action construction contract

In a three-group extension of a normal A₃-block, its natural four-element
module extends the canonical map from the block to its core quotient
to the overgroup. This definition specifies the construction proved in
`AlternatingThree`; it does not assume a splitting. The rank-transfer module derives
splitting modulo the two-core from such a homomorphism.

The ambient normality is relative to J throughout. No rank restriction is
needed in the construction, and no action on a chosen layer is assumed
faithful. The module action and its kernel must be proved from C.1.7 and C.1.12.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), C.1.7--13,
printed pp.123--125, and the proof of E.6.14, printed p.251.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection

/-- Extend the actual A₃ core-quotient map across a three-group extension. -/
def AlternatingThreeQuotientRetractionInput (G : Type*) [Group G] : Prop :=
  ∀ J L : Subgroup G, L ≤ J → ∀ hn : (L.subgroupOf J).Normal,
    ChapterC.IsAlternatingBlock L 3 →
      letI := hn
      IsPGroup 3 (J ⧸ L.subgroupOf J) →
        ∃ r : J →* ((L.subgroupOf J) ⧸ pCore 2 (L.subgroupOf J)),
          ∀ l : L.subgroupOf J,
            r (l : J) = QuotientGroup.mk' (pCore 2 (L.subgroupOf J)) l

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
