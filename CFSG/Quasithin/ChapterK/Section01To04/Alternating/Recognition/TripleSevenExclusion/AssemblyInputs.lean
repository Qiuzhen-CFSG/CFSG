module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Branches
public import Theory.Representation.Quotient

/-!
# Contracts for the triple-seven representation exclusion

The source K.1 exclusion combines an intrinsic representation calculation for
the genuine triple cover of `A₇` with a restriction theorem for small ambient
actors. These contracts retain both obligations and the actual component
equivalence. `Intrinsic` and `OuterBound` prove them separately; the parent
module assembles the full exclusion without further assumptions.

Source: Aschbacher--Smith, K.1, printed p.452/PDF p.463, invoking
Guralnick--Malle (2002), Theorem 6.2 and Table 6.3.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open GLS3.Chapter5.OddCentralCovers

namespace CFSG.Quasithin.ChapterK.Alternating.RecognitionInputs

universe u v

/-- The intrinsic representation exclusion for the genuine
triple cover.  It is deliberately stated for the actual carrier and retains
the full cubic threshold. -/
def TripleSevenIntrinsicExclusion : Prop :=
  ∀ {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (τ : Representation (ZMod 2) TripleSeven W),
    Function.Injective τ → Representation.IsIrreducible τ →
    cubicRatio τ ≤ 2 → False

/-- The ambient-to-component ratio step is a separate representation
obligation.  An outer involution need not lie in the component, so the
ambient cubic bound cannot be silently rewritten as a bound for the
restricted action. -/
def TripleSevenRestrictionBound : Prop :=
  ∀ {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (K : GroupClass.{u}) (L : Subgroup G),
    (h : Input ρ K L) → (e : L ≃* TripleSeven) →
      cubicRatio ((ρ.comp L.subtype).comp e.symm.toMonoidHom) ≤ 2

end CFSG.Quasithin.ChapterK.Alternating.RecognitionInputs

namespace CFSG.Quasithin.ChapterK.Alternating
open RecognitionInputs

universe u v

/-- Transport an intrinsic triple-seven exclusion through the actual
component equivalence appearing in the K.1 input. -/
theorem tripleSevenExclusion_of_intrinsic
    (hmodel : TripleSevenIntrinsicExclusion.{v})
    (hbound : TripleSevenRestrictionBound.{u,v}) :
    TripleSevenExclusion.{u,v} := by
  intro G V _ _ _ _ _ ρ K L h e
  let τ : Representation (ZMod 2) TripleSeven V :=
    (ρ.comp L.subtype).comp e.symm.toMonoidHom
  have hτf : Function.Injective τ := by
    exact (h.faithful.comp L.subtype_injective).comp e.symm.injective
  have hτi : Representation.IsIrreducible τ := by
    change Representation.IsIrreducible
      ((ρ.comp L.subtype).comp e.symm.toMonoidHom)
    exact (irreducible_comp_surjective_iff
      e.symm.toMonoidHom e.symm.surjective (ρ.comp L.subtype)).mpr h.irreducible
  have hτc : cubicRatio τ ≤ 2 := by
    exact hbound ρ K L h e
  exact hmodel τ hτf hτi hτc

end CFSG.Quasithin.ChapterK.Alternating
