module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.SourceClassification.MarkedField
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Identification

/-!
# The source classification witness on the actual temporary image

The full earlier alternatives and the source marker bound supply natural SL₂
coordinates on the whole fixed quotient. The marked maximum-family comparison
identifies the literal image of J(S_E) with its compatible Sylow. Simultaneous
inner transport of the actor and module coordinates therefore places this
image in the standard upper unipotent subgroup, supplying exactly the Borel
normalizer witness required by the existing unreduced alternative.

The identification consumer restricts the field, identifies the action with
the S₃ plane, and proves dimension two and index three for the literal marker.
Only the universal adequate earlier classifier remains an explicit input.
The actual original-I₀ comparison is applied in the Application module.

Source: Aschbacher–Smith, proof of 15.3.67, printed pp.1153–1154, using
B.4.2(1), B.5.1 and B.5.6 (combined manuscript of 1 March 2004).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SourceClassification
open BestReduction BestReduction.SourceAssembly BestReduction.FullCoreTransfer
  Replacement.Transvections ChapterB.SourceInduction
universe u
variable {G L X : Type u} [Group G] [Finite G] [Group L]
  [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
  {K : GroupClass.{u}} {Y T V E : Subgroup G} [IsMulCommutative V]
  [(Replacement.Transvections.localSpan T V E).Normal]
  [IsElementaryAbelian 2 (Replacement.Transvections.localSpan T V E)]
  {σ : Representation (ZMod 2) ((temporaryLineNormalizer T V E) ⧸ localCore T V E) X}

/-- Construct the previously missing whole-quotient and Borel-normalizer
witness for the literal temporary Thompson image, from the full classifier
and preceding source geometry. No reduced list or terminal conclusion is input. -/
theorem temporary_unreduced_alternative (d : TemporarySource K Y T V E L σ)
    (classify : AdequateClassificationInput.{u,u} K) :
    Nonempty (UnreducedAlternative
      (imageRepresentation (σ.comp (thompsonImage T V E).subtype))
      (TemporarySource.imageThompson (σ := σ) (T := T) (V := V) (E := E))) := by
  obtain ⟨F, ⟨c⟩⟩ := temporary_linearTwo_coordinates d classify
  obtain ⟨c', hc'⟩ := MarkedField.temporary_standard_coordinates d F c
  refine ⟨.linearTwo F.Carrier F.degree F.degree_pos F.card_eq c' ?_⟩
  rw [hc']

/-- The actual temporary image is S₃, with moved dimension two and the
literal marker stabilizer of index three. The unreduced witness is proved
above rather than retained as an extra premise. -/
theorem temporary_identification (d : TemporarySource K Y T V E L σ)
    (classify : AdequateClassificationInput.{u,u} K) :
    offenderSubgroup (σ.comp (thompsonImage T V E).subtype) = ⊤ ∧
    Nonempty (actionImage (σ.comp (thompsonImage T V E).subtype) ≃* Equiv.Perm (Fin 3)) ∧
    Module.finrank (ZMod 2)
      (Coinvariants.ker (imageRepresentation (σ.comp (thompsonImage T V E).subtype))) = 2 ∧
    SmallModels.SymmetricThree.markerStabilizer
      (imageRepresentation (σ.comp (thompsonImage T V E).subtype)) d.marker =
        (d.imageMarked.sylow : Subgroup _) ∧
    (SmallModels.SymmetricThree.markerStabilizer
      (imageRepresentation (σ.comp (thompsonImage T V E).subtype)) d.marker).index = 3 := by
  obtain ⟨a⟩ := temporary_unreduced_alternative d classify
  exact Identification.temporary_identification d classify a

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SourceClassification
