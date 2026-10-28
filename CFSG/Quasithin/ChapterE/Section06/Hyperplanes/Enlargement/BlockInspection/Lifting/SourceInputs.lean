module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Inputs
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.LocalFacts

/-!
# The earlier containment input for block lifting

This is precisely the unique-containment conclusion of 1.2.4, for actual
members of the local family and overgroups with nontrivial two-core.
The SQTK and ambient QTKE hypotheses are discharged by the source owner;
the input here is restricted to subgroups of that same ambient group.
In particular this input cannot be applied to an A₃ block.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Definition 1.2.3 and Lemma 1.2.4, printed p.505.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting

variable (G : Type*) [Group G]

/-- The unique-containment clause of 1.2.4, with its nontrivial-core,
Sylow and genuine local-family premises. This is an earlier-source input. -/
def LocalContainmentInput : Prop :=
  ∀ H : Subgroup G, H ∈ Chapter1.H G →
    ∀ (S : Sylow 2 H) (B : Subgroup H), B ∈ Chapter1.L H S →
      ∃! X : Subgroup H, X.IsCComponent ∧ B ≤ X

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting
