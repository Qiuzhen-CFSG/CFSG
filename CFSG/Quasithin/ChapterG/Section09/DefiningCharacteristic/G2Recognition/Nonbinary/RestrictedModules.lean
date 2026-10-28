module

public import Theory.Representation.G2.RestrictedModules
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.Nonbinary

/-!
# The restricted G₂ factors and the natural action used in G.9.3

The imported four-factor construction supplies genuine absolutely irreducible
actions of the octonion group, of dimensions 1, 6, 14 and 64, with their root
actions, highest weights and coefficient-Frobenius equivalences. The natural
factor's explicit quotient intertwiner restricts to the binary field. Thus a
representation recognized as that factor after scalar extension descends to
the exact natural action in the conclusion of G.9.3(10).

The descent theorem below retains its explicit representation equivalence
premise. Tensor exhaustivity and recognition of arbitrary small-degree modules
belong to the enclosing nonbinary argument.

Source: GLS3, 2.8.6, 2.8.8 and 2.8.10(g); Aschbacher--Smith, G.9.3(10),
printed pp.354,356--357.
-/

@[expose] public noncomputable section

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.Nonbinary

attribute [local instance] ZMod.algebra

open Atlas.G2.Restricted

variable (F : Type*) [Field F] [CharP F 2]

/-- The concrete natural restricted factor, viewed over the binary field. -/
def restrictedNaturalBinary : Representation (ZMod 2) (Atlas.G2.Model F)
    (NaturalCoordinates.Space F) :=
  Representation.restrictScalars (NaturalCoordinates.action F)

/-- Restricting the explicit quotient intertwiner preserves the actual action. -/
def restrictedNaturalBinaryEquiv :
    Representation.RepEquiv (restrictedNaturalBinary F) (naturalBinary F) where
  toLinearEquiv := (show NaturalCoordinates.Space F ≃ₗ[F] Atlas.G2.Natural.Space F from
    (naturalActualEquiv F).toLinearEquiv).restrictScalars (ZMod 2)
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    exact naturalActualEquiv_intertwines F g v

/-- The coordinate model has the same binary degree as the specified quotient model. -/
theorem restrictedNaturalBinary_degree [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    Module.finrank (ZMod 2) (NaturalCoordinates.Space F) = 6 * n :=
  (restrictedNaturalBinaryEquiv F).toLinearEquiv.finrank_eq.trans
    (naturalBinary_degree F hF)

variable {F} [Finite F]
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Once an extended action is identified with the constructed natural factor,
scalar descent gives the actual quotient action, preserving its group twist. -/
theorem natural_of_extended_restricted_equiv
    (ρ : Representation (ZMod 2) (Atlas.G2.Model F) V)
    (K : Type*) [Field K] [Algebra (ZMod 2) K]
    (a : Atlas.G2.Model F ≃* Atlas.G2.Model F)
    (h : Nonempty (Representation.RepEquiv (Representation.extendScalars K ρ)
      (Representation.extendScalars K ((restrictedNaturalBinary F).comp a.toMonoidHom)))) :
    Quasiequivalent ρ (naturalBinary F) := by
  let : FiniteDimensional (ZMod 2) F := Module.Finite.of_finite
  obtain ⟨e⟩ := Representation.repEquiv_of_extendScalars (S := K) ρ
    ((restrictedNaturalBinary F).comp a.toMonoidHom) h
  refine ⟨a, e.toLinearEquiv.trans (restrictedNaturalBinaryEquiv F).toLinearEquiv, ?_⟩
  intro g v
  change restrictedNaturalBinaryEquiv F (e (ρ g v)) =
    naturalBinary F (a g) (restrictedNaturalBinaryEquiv F (e v))
  rw [e.isIntertwining]
  exact (restrictedNaturalBinaryEquiv F).isIntertwining (a g) (e v)

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.Nonbinary
