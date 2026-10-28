module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.Models
public import CFSG.Quasithin.ChapterG.Section09.Setup
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.Nonbinary.PeriodDescent
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.Nonbinary.FrobeniusParameters
public import Theory.Representation.ScalarDescent

/-!
# Schur fields and descent for nonbinary G₂ recognition

`Representation.EndFieldFrobenius` identifies the actual Schur degree with the
exact Frobenius period of the absolutely irreducible Schur model, and proves the
scalar-dimension formula. These statements require no degree bound.

The descent lemma below preserves an actual intertwining equivalence with the
octonion quotient action, allowing a group automorphism to account for a field
twist. It does not infer equivalence from dimensions.

`exists_basic_parameters_and_natural` now combines the four concrete restricted
modules and their exhaustive tensor classification with this descent. It gives
the basic-degree formula for every faithful irreducible binary action, with the
actual Schur degree as block length, and recognizes the single-natural block.
There is no small-degree assumption; the parent supplies that arithmetic
exclusion and the original actor's rank bounds.

Source: Aschbacher--Smith, G.9.3(10), printed pp.354,356--357; GLS3,
2.8.6, 2.8.8 and 2.8.10(g).
-/

public noncomputable section

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.Nonbinary

attribute [local instance] ZMod.algebra

variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) (Atlas.G2.Model F) V)

/-- An equivalence after scalar extension descends to the genuine binary
natural action, retaining the automorphism of the actual G₂ model. This is a
descent helper, not a construction of the required extended equivalence. -/
theorem natural_of_extended_equiv (K : Type*) [Field K] [Algebra (ZMod 2) K]
    (a : Atlas.G2.Model F ≃* Atlas.G2.Model F)
    (h : Nonempty ((Representation.extendScalars K ρ).Equiv
      (Representation.extendScalars K ((naturalBinary F).comp a.toMonoidHom)))) :
    Quasiequivalent ρ (naturalBinary F) := by
  let : FiniteDimensional (ZMod 2) F := Module.Finite.of_finite
  let : FiniteDimensional (ZMod 2) (Atlas.G2.Natural.Space F) :=
    Module.Finite.trans F (Atlas.G2.Natural.Space F)
  obtain ⟨f⟩ := Representation.repEquiv_of_extendScalars (S := K) ρ
    ((naturalBinary F).comp a.toMonoidHom)
      (h.map Representation.RepEquiv.ofRepresentationEquiv)
  refine ⟨a, f.toLinearEquiv, ?_⟩
  intro g v
  exact f.isIntertwining g v

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.Nonbinary
