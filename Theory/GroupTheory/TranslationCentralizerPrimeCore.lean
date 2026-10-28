module

public import Theory.GroupTheory.SemidirectProductTranslationCentralizer
public import Theory.PGroupCore

/-!
# The prime core of a faithful affine translation centralizer

For an abelian p-group of translations and a faithful linear action, the
translation kernel in an element centralizer is normal and self-centralizing.
It lies in the intrinsic p-core, which is therefore self-centralizing too.
The calculation retains the literal projection to the vector stabilizer.

This supplies the characteristic-two input in Aschbacher–Smith 12.2.27,
printed p.807, before its extraspecial local calculation.
-/

public section
open Subgroup
namespace Theory.GroupTheory.TranslationCentralizer
variable {U B : Type*} [CommGroup U] [Group B] (φ : B →* MulAut U) (v : U)

theorem pCore_selfCentralizing {p : ℕ} [Fact p.Prime]
    (hu : IsPGroup p U) (hφ : Function.Injective φ) :
    Subgroup.centralizer (pCore p (centralizer φ v) : Set (centralizer φ v)) ≤
      pCore p (centralizer φ v) := by
  have hk : (projection φ v).ker ≤ pCore p (centralizer φ v) :=
    le_sSup ⟨inferInstance, hu.of_equiv (kernelEquiv φ v)⟩
  exact (Subgroup.centralizer_le hk).trans ((kernel_selfCentralizing φ v hφ).trans hk)

end Theory.GroupTheory.TranslationCentralizer
