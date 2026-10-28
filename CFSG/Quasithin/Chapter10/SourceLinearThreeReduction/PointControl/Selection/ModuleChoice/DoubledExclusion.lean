module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.NormalizerIrreducibility
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.BinaryThreeRecognition
public import Theory.Representation.BinaryDoubledNaturalMultiplicity

/-!
# Excluding the doubled row on a minimal full module

The component normalizer acts irreducibly on the original moved quotient by
minimality and crossed centralization. In the doubled SL₃(2) row its action
on multiplicities has solvable image. The actual cubic residual makes that
image prime to three, so it is a two-group and preserves a proper natural
copy. This contradicts irreducibility.

Consequently every moving local Thompson branch on a minimal full module has
one of the two literal natural rows, with its original fixed kernel retained.
The applications in ModuleChoice.Source supply full/local equality, crossed
support and the conditional point-selection conclusion on the same setup.
Source: Aschbacher--Smith, B.5.6, D.3.21, 3.2.6 and10.1.1--3,
printed pp.105,204--207,581 and741--742.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Minimality and the actual cubic residual exclude the literal doubled row;
no constituent or fixed-kernel assertion is assumed. -/
theorem not_binaryThreeDoubled_of_minimal
    (hmin : D.IsMinimalFullModule)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    ¬ BinaryThreeDoubled D := by
  intro hd
  obtain ⟨e,⟨c⟩⟩ := hd
  let σ := Representation.SL3DoubledNaturalOffenders.representation (ZMod 2)
  have hs : repeated (linearNatural BinaryField.two 3) 2 = σ := by
    ext g v i j
    rfl
  rw [hs] at c
  obtain ⟨ρ,f,hi,hf,⟨cN⟩⟩ := exists_irreducible_moved_normalizer D hmin ht htn hcross
    σ (Representation.SL3DoubledNaturalOffenders.representation_injective (ZMod 2)) e c
  have hd3 : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
    rw [Nat.card_congr e.toEquiv,Matrix.PSL3Two.card_SL]
    decide
  let := Representation.SL3DoubledNaturalOffenders.binary_multiplicity_solvable
  have hc := normalizer_solvable_image_three_free D (fun hn => htn (hn ht)) hd3
    (Representation.SL3DoubledNaturalOffenders.binaryMultiplicity.comp f)
  have hp := Representation.SL3DoubledNaturalOffenders.binary_multiplicity_twoGroup_of_three_free _ hc
  have he : ((Representation.SL3DoubledNaturalOffenders.action (ZMod 2)).comp
      ((Representation.SL3DoubledNaturalOffenders.normalizer (ZMod 2)).subtype.comp f)) = ρ := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    exact hf g v
  apply Representation.SL3DoubledNaturalOffenders.not_irreducible_of_binaryMultiplicity_twoGroup f hp
  rwa [he]

/-- The moving local Thompson branch has only the two literal natural rows
on every original minimal full module. -/
theorem moving_local_natural_of_minimal
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hJ : ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G)) : RankOneNatural D ∨ BinaryThreeNatural D := by
  rcases moving_local_natural_or_doubled D hn hna hJ with hr | ht | hd
  · exact Or.inl hr
  · exact Or.inr ht
  · obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
    exact (not_binaryThreeDoubled_of_minimal D hmin ht htn
      (crossed_of_local_thompson D hJ ht htn) hd).elim

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
