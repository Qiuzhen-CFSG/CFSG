module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.BorelPlacement.CentralProduct
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel.SylowCoordinates
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel.CharacteristicControl

/-!
# Assembly of a characteristic-controlled block Borel

The Sylow coordinates identify the first residual Borel lift with the
actual subgroup O²(N_{K₁}(U ∩ K₁)). Once that subgroup is placed in C(G,R),
conjugation by the exchanger places the second lift there too. Thus the
published image of the full product Borel lies in C(G,R), over the field
and with the natural-module model furnished by the source block type.

The characteristic-control theorem places the first residual in the normalizer
of the nontrivial characteristic subgroup J(R). Applying the assembly lemma
therefore constructs the required field, natural-module model and full pair
Borel from the contrary data and explicit commutation of the exchanged blocks.
Discharging commutation and deriving the field-four bound remain with the
parent proof of 15.4.20.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of 15.4.20, printed p.1164, final characteristic-two paragraph.
-/

@[expose] public section

open Subgroup CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {d : Source.Geometry G} {i j : Bool}
variable {c : ContraryData κ d i j} (b : ExchangedBlock c)

/-- Assemble the requested field, actual model and full pair Borel from
characteristic control of the first intrinsic Sylow-normalizer residual. -/
theorem exists_controlled_model_of_firstSylowResidual_le
    (hc : ⁅b.first, ExchangedBlock.second b⁆ = ⊥)
    (hfirst : firstSylowResidual b ≤
      characteristicNormalizerClosure ((d.wholeX ⊔ c.U : Subgroup G).pCoreIn 2)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2 ^ b.n ∧
      ∃ m : BlockModuleModel b.first (Matrix.SL2.naturalAction F),
        ExchangedBlock.ambientBorel b hc m ≤
          characteristicNormalizerClosure ((d.wholeX ⊔ c.U : Subgroup G).pCoreIn 2) := by
  obtain ⟨F, hF, hfin, hchar, hcard, m, hm⟩ := exists_aligned_model b
  refine ⟨F, hF, hfin, hchar, hcard, m, ?_⟩
  apply ambientBorel_le_of_firstLift b hc m _
    (exchanger_mem_characteristicNormalizerClosure b)
  rwa [firstLift_eq_firstSylowResidual b m hm]

/-- The exchanged blocks admit compatible natural-module coordinates in which
the full pair Borel lies in C(G,R), where R = O₂(XU). The only additional
structural hypothesis is commutation of the two actual blocks. -/
theorem exists_controlled_model
    (hc : ⁅b.first, ExchangedBlock.second b⁆ = ⊥) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2 ^ b.n ∧
      ∃ m : BlockModuleModel b.first (Matrix.SL2.naturalAction F),
        ExchangedBlock.ambientBorel b hc m ≤
          characteristicNormalizerClosure ((d.wholeX ⊔ c.U : Subgroup G).pCoreIn 2) :=
  exists_controlled_model_of_firstSylowResidual_le b hc
    (firstSylowResidual_le_characteristicNormalizerClosure c b hc)


end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel
