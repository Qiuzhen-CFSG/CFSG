module
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.CommutationSource
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.CharacteristicTwoBlocks
/-!
# Characteristic-two component lifting from proved block commutation

The exact C.1.9 source theorem discharges the A₃-block centralization input.
The original E.6.7 decomposition then contains a nonsolvable block factor
conjugate to the given C-component by the prescribed Sylow centralizer.
This retains the literal factor, conjugating element, quotient, natural module,
and ambient subnormality. The independent E.6.7 and A.3.8 source inputs remain
with their producers; no block-commutation input remains.

Source: Aschbacher–Smith, C.1.9/29, E.6.7/23, and A.3.8.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting
open InvariantSubspaces.BlockSelection CharacteristicTwoBlocks
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

namespace CharacteristicTwoBlocks

/-- Actual A₃ blocks are centralized by C-components under the original local hypotheses. -/
theorem source_threeBlockCentralization : ThreeBlockCentralization κ G :=
  threeBlockCentralization_of_blockCommutation (source_blockCommutationInput G)

end CharacteristicTwoBlocks

/-- The original decomposition contains an actual Sylow conjugate factor, with
its solvable-block centralization supplied by C.1.9. -/
theorem exists_factor_conjugate_of_source_blockCommutation
    {T : Sylow 2 G} {M V A X : Subgroup G}
    (h : HypothesisE61 κ T M V) (h67 : E67Input T M V)
    (h38 : SylowOrbitSource κ)
    (hA : A ∈ obstructionFamily M V)
    (hX : X ∈ Chapter1.cComponentsIn (centralizer (A : Set G))) (hXM : ¬ X ≤ M)
    (hf : generalizedFitting ↥(X ⊔ sylowCentralizer (T : Subgroup G) V) =
      pCore 2 ↥(X ⊔ sylowCentralizer (T : Subgroup G) V)) :
    ∃ d : E67Decomposition (sylowCentralizer (T : Subgroup G) V) M V A
        (X ⊔ sylowCentralizer (T : Subgroup G) V),
      ∃ i, ∃ s ∈ sylowCentralizer (T : Subgroup G) V,
        d.block i = X.map (MulAut.conj s).toMonoidHom :=
  exists_factor_conjugate h h67 h38 source_threeBlockCentralization hA hX hXM hf

/-- The characteristic-two lifting branch uses the actual C.1.9 theorem. -/
theorem characteristicTwoComponentBlocks_of_source_blockCommutation
    {M V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
    (h : HypothesisE61 κ T M V) (h15 : HypothesisE615 V)
    (h67 : E67Input T M V) (h38 : SylowOrbitSource κ) :
    CharacteristicTwoComponentBlocks (sylowCentralizer (T : Subgroup G) V) M V :=
  characteristicTwoComponentBlocks h h15 h67 h38 (source_blockCommutationInput G)
end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting
