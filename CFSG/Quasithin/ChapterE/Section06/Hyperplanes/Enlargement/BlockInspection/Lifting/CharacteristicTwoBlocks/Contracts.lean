module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Inputs
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Contracts

/-!
# The orbit input and solvable-block obligation for characteristic-two lifting

The first predicate is the Sylow-orbit assertion explicitly stated in
A.3.8(3), restricted to the case where the component and Sylow subgroup
generate the ambient group. Its trivial-two-core hypothesis is retained.
The second predicate is a new obligation: it is not included in E.6.7 or
assumed to be an earlier source theorem. It separates the solvable-block
calculus from identification of the nonsolvable decomposition factors.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.3.8(3),
printed p.45; E.6.7 and E.6.23, printed pp.246 and 254.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting
namespace CharacteristicTwoBlocks
universe u

/-- The orbit-exhaustion clause of A.3.8(3) in a generated overgroup.
This is an authorized exact earlier-source input, with all its hypotheses. -/
def SylowOrbitSource (κ : GroupClass.{u}) : Prop :=
  ∀ (D : Type u) [Group D] [Finite D], IsSQTK κ D → pCore 2 D = ⊥ →
    ∀ (S : Sylow 2 D) (X : Subgroup D), X.IsCComponent → X ⊔ S = ⊤ →
      ∀ B : Subgroup D, B.IsCComponent →
        ∃ s : S, B = X.map (MulAut.conj (s : D)).toMonoidHom

/-- Remaining block calculus, to be proved from the genuine earlier inputs.
Both subnormality and C-component membership are relative to H. The actual
A₃ conjugation module is retained. No escaping-component classification
is part of this contract. -/
def ThreeBlockCentralization (κ : GroupClass.{u}) (G : Type u) [Group G] : Prop :=
  ∀ H : Subgroup G, IsSQTK κ H → generalizedFitting H = pCore 2 H →
    ∀ B X : Subgroup G, B ≤ H → X ≤ H →
      ChapterC.IsAlternatingBlock B 3 → (B.subgroupOf H).IsSubnormal →
      (X.subgroupOf H).IsCComponent → X ≤ centralizer (B : Set G)

end CharacteristicTwoBlocks
end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting
