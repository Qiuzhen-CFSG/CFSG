module

public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.Cases
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.Reduction

/-!
# The remaining local inputs to the characteristic-two case of 12.4.8

This is the same-G,T version of the corresponding CentralizerBound proof.
Its configuration carries only Structural1222At at the original Sylow;
every subgroup, action and relative component map is unchanged.

These contracts separate the actual L₃ hyperplane stabilizer from the two
local arguments in E.6.14. The block-selection contract may use the faithful
cubic actor supplied by the geometry. The index contract concerns the same
literal block inside C_G(U), with A = LT; it does not require a theorem about
arbitrary SQTK amalgams. Geometry.lean constructs the stabilizer input. Block selection and the
local index calculation must still be proved before the exclusion is complete.

Source: Aschbacher–Smith, 12.4.8, printed p.815, and E.6.14, printed p.251.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.CharacteristicTwo
open ChapterE.Section06 ChapterE.Section06.InvariantSubspaces
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V U : Subgroup G}

/-- The stabilizer and actual cubic subgroup required by E.6.14(ii),(iii). -/
structure StabilizerGeometry (T : Sylow 2 G) (L U : Subgroup G) : Prop where
  faithful_three : HasFaithfulThreeAction U
  maximal : localNormalizer (L ⊔ (T : Subgroup G)) U ⋖ L ⊔ (T : Subgroup G)
  index_ne_two : (localNormalizer (L ⊔ (T : Subgroup G)) U).relIndex
    (L ⊔ (T : Subgroup G)) ≠ 2

/-- Selection of the actual residual block, allowing the independent geometric input. -/
def BlockSelection (_c : Configuration T L V U) : Prop :=
  HasCharacteristicTwo (centralizer (U : Set G)) → HasFaithfulThreeAction U →
    ∃ J : Subgroup G, SingleBlock T (normalizer (V : Set G)) V U J ∧
      (ChapterC.IsAlternatingBlock J 3 ∨ ChapterC.IsAlternatingBlock J 5)

/-- The localized C.5.7 calculation for the literal selected block and LT.
The characteristic-two premise is on C_G(U), not on ambient G. -/
def BlockIndex (_c : Configuration T L V U) : Prop :=
  HasCharacteristicTwo (centralizer (U : Set G)) →
    ∀ J : Subgroup G, SingleBlock T (normalizer (V : Set G)) V U J →
      (ChapterC.IsAlternatingBlock J 3 ∨ ChapterC.IsAlternatingBlock J 5) →
      localNormalizer (L ⊔ (T : Subgroup G)) J ⋖ L ⊔ (T : Subgroup G) →
      (localNormalizer (L ⊔ (T : Subgroup G)) J).relIndex
        (L ⊔ (T : Subgroup G)) = 2

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.CharacteristicTwo
