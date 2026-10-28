module

public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.RudvalisExclusion.SmallModuleRecognition.GeneratorIntertwiner.TraceInputs
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.RudvalisExclusion.SmallModuleRecognition.GeneratorIntertwiner.Irreducibility
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.TraceComparison
public import Theory.Representation.PRegularTrace
public import Mathlib.Algebra.Module.ULift

/-!
# Constructing a Rudvalis generator intertwiner from odd-order traces

The fixed degree-28 matrix action is irreducible by the order-29 argument.
Equality of traces on odd-order elements extends to all elements by taking
the odd part. Jacobson density then identifies the given absolutely simple
module with the fixed simple module over F₂ itself. Restricting this actual
equivalence to the two marked generators gives the requested nonzero map.
An explicit universe lift retains the contract's arbitrary universe for V.

The exhaustive odd-order trace calculation remains an explicit premise.
This is a conditional reduction, not the unconditional degree-28 recognition
theorem. Source: Hiss--Malle, corrected Table 2, p.102; application to the Ru
paragraph of Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1.
-/

public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue.RudvalisExclusion
open Representation SmallModuleRecognitionInputs
universe v

private theorem equiv_of_odd_trace
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) Rudvalis.Model V)
    (τ : Representation (ZMod 2) Rudvalis.Model Space)
    [σ.IsAbsolutelyIrreducible] [τ.IsIrreducible]
    (htrace : ∀ g, ¬ 2 ∣ orderOf g → σ.character g = τ.character g) :
    Nonempty (σ.Equiv τ) := by
  let E : ULift.{v} Space ≃ₗ[ZMod 2] Space := ULift.moduleEquiv
  let τ' : Representation (ZMod 2) Rudvalis.Model (ULift.{v} Space) :=
    E.symm.conjRingEquiv.toMonoidHom.comp τ
  let eτ : τ'.Equiv τ := .mk E (fun g => by
    ext x
    simp [τ'])
  let : τ'.IsIrreducible :=
    (RepEquiv.irreducible_euqiv (RepEquiv.ofRepresentationEquiv eτ)).mpr inferInstance
  have hc : σ.character = τ'.character := by
    funext g
    obtain ⟨x, hx, hh⟩ := exists_pRegular_same_character (F := ZMod 2) 2 g
    exact (hh V σ).trans ((htrace x hx).trans
      ((congrFun (char_iso eτ) x).symm.trans (hh (ULift.{v} Space) τ').symm))
  obtain ⟨f⟩ := SU3.FiveSmallModules.SevenRestriction.Twenty.equiv_of_equal_trace σ τ' hc
  exact ⟨f.trans eτ⟩

/-- Application of the scalar calculation to the exact published contract.
The fixed action's irreducibility is proved here, not included in the input. -/
theorem degree28GeneratorIntertwining_of_oddTraceComparison
    (htrace : Degree28OddTraceComparison.{v}) : Degree28GeneratorIntertwining.{v} := by
  intro e ha hb hq V _ _ _ σ hf hi hd
  let := hi
  let τ : Representation (ZMod 2) Rudvalis.Model Space :=
    standardRepresentation.comp e.toMonoidHom
  let : τ.IsIrreducible := GeneratorIntertwiner.pulledStandard_isIrreducible e
  obtain ⟨f⟩ := equiv_of_odd_trace σ τ (htrace e ha hb hq V σ hf hi hd)
  refine ⟨f.toLinearMap, ?_, ?_, ?_⟩
  · intro hz
    have h := LinearMap.congr_fun hz (f.symm (1 : Space))
    change f (f.symm (1 : Space)) = 0 at h
    rw [f.apply_symm_apply] at h
    exact one_ne_zero h
  · intro v
    have h := LinearMap.congr_fun (f.isIntertwining' Rudvalis.a) v
    change f (σ Rudvalis.a v) = (e Rudvalis.a).val.val (f v) at h
    rw [ha] at h
    exact h
  · intro v
    have h := LinearMap.congr_fun (f.isIntertwining' Rudvalis.b) v
    change f (σ Rudvalis.b v) = (e Rudvalis.b).val.val (f v) at h
    rw [hb] at h
    exact h

end CFSG.Quasithin.ChapterK.SporadicCatalogue.RudvalisExclusion
