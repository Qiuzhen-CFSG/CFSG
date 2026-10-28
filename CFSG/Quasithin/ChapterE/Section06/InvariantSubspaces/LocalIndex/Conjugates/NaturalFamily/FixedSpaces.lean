module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Reduction

/-!+# The full fixed-space calculation needed by the natural family

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
C.5.6(1)–(5), printed pp.156–157, and C.5.7, printed p.160.

Write `E = UˣD`. Every element of `S` outside `Q` has the same fixed
subgroup in `Q`, namely `Q ∩ E`. This identifies `E` with the conjugate
core and hence gives equal orders. The identity concerns the full groups, including the
central fixed layer of `U`. The natural quotient alone does not provide
them. The family reduction uses counting for maximality and B.2.21 for
uniqueness of the lift of the nontrivial actor.

The two input definitions below are outstanding model calculations. They
contain neither a maximum-family assertion nor a local normalizer index.
Their separate owners must prove them before `NaturalFamilyInput` can be
discharged. In particular the natural `L₂(4)` branch retains its defining
module and is separate from the alternating-five permutation module.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.NaturalFamily

open Subgroup
universe u
variable {G : Type u} [Group G]

/-- The full fixed subgroups of every actor outside the core. This is a module
calculation, not an assumed classification of elementary subgroups. -/
structure FixedSpaceCalculation (R L : Subgroup G) (x : G) : Prop where
  fixed : ∀ s ∈ S R, s ∉ Q R L →
    Q R L ⊓ centralizer ({s} : Set G) = Q R L ⊓ opposite R L x

/-- The defining natural-module branch, including the field of order four. -/
def LinearInput [Finite G] (K : GroupClass.{u}) : Prop :=
  ∀ A H R L : Subgroup G, Configuration K A H R L → BaumannStructure H R L →
    (∃ n, ChapterC.IsL2EvenBlock L n) →
    ∀ x ∈ A, ¬ (U L).map (MulAut.conj x).toMonoidHom ≤ centralizer (U L : Set G) →
      Factorization R L x → F R L = ⊥ → FixedSpaceCalculation R L x

/-- The binary two-dimensional module for the block with quotient `A₃`. -/
def AlternatingThreeInput [Finite G] (K : GroupClass.{u}) : Prop :=
  ∀ A H R L : Subgroup G, Configuration K A H R L → BaumannStructure H R L →
    ChapterC.IsAlternatingBlock L 3 →
    ∀ x ∈ A, ¬ (U L).map (MulAut.conj x).toMonoidHom ≤ centralizer (U L : Set G) →
      Factorization R L x → F R L = ⊥ → FixedSpaceCalculation R L x

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.NaturalFamily
end
