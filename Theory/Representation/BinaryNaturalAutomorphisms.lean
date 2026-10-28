module
public import Theory.Representation.BinaryNaturalFullAction
public import Theory.Representation.GeneralLinearNatural

/-!
# The binary natural action as a group of automorphisms

The standard SLₙ(2) action is a multiplicative automorphism of the additive
natural module. Faithfulness and the full binary action identify SLₙ(2)
with its entire automorphism group. The action retains the usual matrix
formula, allowing literal conjugation models to transport through this map.

Source application: Aschbacher--Smith, 12.2.24, printed p.804.
-/

public section
namespace Representation
@[expose] noncomputable def binaryNaturalAut (d : ℕ) :
    Matrix.SpecialLinearGroup (Fin d) (ZMod 2) →*
      MulAut (Multiplicative (Fin d → ZMod 2)) where
  toFun a := (Matrix.SpecialLinearGroup.toLin' a).toAddEquiv.toMultiplicative
  map_one' := by
    apply MulEquiv.ext
    intro x
    change Representation.specialLinearNatural d 1 x.toAdd = x.toAdd; rw [map_one]; rfl
  map_mul' a b := by
    apply MulEquiv.ext
    intro x
    change Representation.specialLinearNatural d (a*b) x.toAdd =
      Representation.specialLinearNatural d a (Representation.specialLinearNatural d b x.toAdd)
    rw [map_mul]
    rfl

theorem binaryNaturalAut_bijective (d : ℕ) : Function.Bijective (binaryNaturalAut d) := by
  constructor
  · intro a b he
    apply Representation.specialLinearNatural_injective d
    apply LinearMap.ext
    intro x
    exact congrArg (fun z : MulAut (Multiplicative (Fin d → ZMod 2)) => (z (Multiplicative.ofAdd x)).toAdd) he
  · intro a
    obtain ⟨g,hg⟩ := Representation.specialLinearNatural_binary_full d a
    exact ⟨g, MulEquiv.ext hg⟩


end Representation
