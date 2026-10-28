module

public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockReductionRows
public import Theory.SpecificGroups.PSL3Two.Cardinality
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder

/-!
# Recovering the original marked L₃ extension at G,T

The seven source module alternatives reduce, when the fixed space is nonzero,
to four actual marked modules. The original quotient has order 168, excluding
the alternating and G₂ actors. The surviving four-dimensional row supplies
the marked natural quotient on the original V, with its conjugation equation.
No fusion, fixed-space vanishing, or universal module classification is used.

Source: Aschbacher–Smith, 12.2.2(3), p.795, and 12.4.5, p.813.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.At
open Section02 Section02.RecognitionSource
open Section02.RecognitionSource.FusionReducibleNormalizer
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G}

/-- The marked implication restricted to the original ambient group and Sylow.
It contains no assertion about another Sylow subgroup or ambient group. -/
@[expose] def SLThreeAlternative1222At (K : GroupClass.{u}) (T : Sylow 2 G) : Prop :=
  ∀ L V : Subgroup G, Hypothesis1223 K T L → (D : ChosenModule T L V) →
    ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2 → fixedSubgroup L V ≠ ⊥ →
    Nonempty (SLThreeExtension D)

/-- Recover the extension from the original local seven-row source statement. -/
theorem extension_of_modules
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) : Nonempty (SLThreeExtension D) := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := hmodel
  let : Field F := hF
  let : Finite F := hfin
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hc)
  let e₀ := (e.trans (Atlas.fieldEquivPSL 3 eF)).trans Matrix.PSL3Two.equiv.symm
  have hcard : Nat.card (L ⧸ pCore 2 L) = 168 :=
    (Nat.card_congr e₀.toEquiv).trans Matrix.PSL3Two.card_SL
  cases reducibleModels_of_module_alternatives h D hne (modules L V h D) with
  | linearThree E => exact ⟨E⟩
  | alternatingSix E =>
      let := D.actionCentralizer_normal
      have hb := Nat.card_le_card_of_surjective D.coreToFaithful D.coreToFaithful_surjective
      rw [hcard, Nat.card_congr E.groupEquiv.toEquiv,
        nat_card_alternatingGroup, Nat.card_fin] at hb
      norm_num [Nat.factorial] at hb
  | alternatingEight E =>
      have he := Nat.card_congr E.groupEquiv.toEquiv
      rw [hcard, nat_card_alternatingGroup, Nat.card_fin] at he
      norm_num [Nat.factorial] at he
  | g2 E =>
      have he := Nat.card_congr E.groupEquiv.toEquiv
      rw [hcard, Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at he
      norm_num at he

/-- Supply the precise local marked input from the seven original source rows. -/
theorem alternative_of_modules
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T) :
    SLThreeAlternative1222At KnownSimple.IsKnownSimple T :=
  fun _ _ h D hmodel hne => extension_of_modules h D modules hmodel hne

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.At
