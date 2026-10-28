module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.MathieuLocalSections.Reduction
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Two independent action steps for octad placement

The local C-component condition should force the Sylow subgroup to normalize
B. Once this holds, the quotient of B joined with S by B is a two-group.
The second step excludes a transitive action of such a join on the 24 points
when B/O₂(B) is L₄(2). Neither step is assumed to follow from order bounds.

These two remaining contracts separate the component argument from the
permutation-action argument. The latter can use normalization as an explicit
hypothesis while the former is proved independently. The placement assembly
must discharge both contracts.

Source: Aschbacher–Smith, A.3.12(14) and its sporadic Sylow-overgroup argument,
printed pp.47–48; GLS3, Table 5.3e. The action is that of the native W24
automorphism group throughout.
-/

public section

namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.MathieuLocalSections

open Subgroup Sporadic.Mathieu
open CFSG.Quasithin.Chapter1

/-- Relative normalization of the source component, not ambient normality in M₂₄. -/
@[expose] def LocalNormalization : Prop :=
  ∀ (B : Subgroup M24) (S : Sylow 2 M24),
    ClassicalGroup.IsPSL (XiQuotient B) 4 2 →
    B ∈ ChapterA.Section03.localCComponents S →
    S.toSubgroup ≤ normalizer (B : Set M24)

/-- The action step may take normalization explicitly, independently of the
local C-component argument. Its conclusion is about the actual 24 points. -/
@[expose] def NormalizedJoinIntransitivity : Prop :=
  ∀ (B : Subgroup M24) (S : Sylow 2 M24),
    ClassicalGroup.IsPSL (XiQuotient B) 4 2 →
    S.toSubgroup ≤ normalizer (B : Set M24) →
    ¬ MulAction.IsPretransitive (B ⊔ S.toSubgroup : Subgroup M24) (Fin 24)

/-- Normalization makes the relative index a power of two. The proof takes
the quotient inside the join, where the supplied normalization is sufficient. -/
theorem normalized_join_index_two_power (B : Subgroup M24) (S : Sylow 2 M24)
    (hn : S.toSubgroup ≤ normalizer (B : Set M24)) :
    ∃ n : ℕ, B.relIndex (B ⊔ S.toSubgroup) = 2 ^ n := by
  let H := B ⊔ S.toSubgroup
  let C := B.subgroupOf H
  let R := S.toSubgroup.subgroupOf H
  let : C.Normal := normal_subgroupOf_of_le_normalizer (sup_le B.le_normalizer hn)
  have hp : IsPGroup 2 (H ⧸ C) := by
    apply isPGroup_quotient_of_sup_eq_top C R S.isPGroup'.comap_subtype
    exact (codisjoint_subgroupOf_sup B S.toSubgroup).eq_top
  exact hp.exists_card_eq

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.MathieuLocalSections
