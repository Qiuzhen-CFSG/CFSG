module

public import Theory.SpecificGroups.BinaryLinear.Affine
public import Theory.GroupTheory.TranslationCentralizerPrimeCore

/-!
# Self-centralizing cores in the binary affine point centralizers

The literal special-linear action on column vectors is faithful. Applying
the translation-centralizer theorem identifies the intrinsic two-core as
self-centralizing, without a choice of coordinates for a specific vector.

Source application: Aschbacher–Smith 12.2.27, printed p.807.
-/

public section
open Subgroup
namespace BinaryLinear.Affine

theorem action_injective (d : ℕ) : Function.Injective (action d) := by
  intro a b h
  apply Matrix.SpecialLinearGroup.toLin'_injective
  apply LinearEquiv.ext
  intro v
  exact congrArg Multiplicative.toAdd (DFunLike.congr_fun h (Multiplicative.ofAdd v))

theorem point_core_selfCentralizing (d : ℕ) (v : Multiplicative (Fin d → ZMod 2)) :
    centralizer (pCore 2 (Theory.GroupTheory.TranslationCentralizer.centralizer (action d) v) :
      Set (Theory.GroupTheory.TranslationCentralizer.centralizer (action d) v)) ≤
      pCore 2 (Theory.GroupTheory.TranslationCentralizer.centralizer (action d) v) :=
  Theory.GroupTheory.TranslationCentralizer.pCore_selfCentralizing (action d) v
    ZModModule.isPGroup_multiplicative (action_injective d)

end BinaryLinear.Affine