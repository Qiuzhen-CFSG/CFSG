module

public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.RudvalisExclusion.Contracts
public import Theory.Representation.AbsolutelyIrreducible

/-!
# Inputs for recognition of the small binary Rudvalis module

The multiplier bound, absolute degree calculation, and construction of a
nonzero intertwiner are separate mathematical obligations. None is asserted
by the definitions below. The assembly in `SmallModuleRecognition` removes
central covers, descends the degree calculation through the actual Schur
field, and promotes the generator intertwiner to a linear equivalence.

The source group hypotheses are inherited from the original quasisimple
group; intrinsic order and simplicity certification is not required here.
Sources: Aschbacher--Smith, printed pp.407, 451, 457; Guralnick--Malle,
Classification of 2F-modules I, Proposition 5.1 (Ru); Hiss--Malle, corrected
Table 2, the characteristic-two degree-28 Ru row on p.102.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue.RudvalisExclusion
namespace SmallModuleRecognitionInputs
open Theory.GroupTheory Subgroup
universe u v

/-- The upper-bound consequence of the Ru multiplier calculation. The existing
multiplier owner must supply it; a double cover alone does not suffice. -/
def TwoPrimaryCoverCenters : Prop :=
  ∀ {L : Type u} [Group L] [Finite L] [IsQuasisimple L],
    Nonempty (L ⧸ center L ≃* Rudvalis.Model) → IsPGroup 2 (center L)

/-- Only the absolute degree window is requested, over every finite field of
characteristic two. This does not identify any representation. -/
def AbsoluteDegreeWindow : Prop :=
  IsQuasisimple Rudvalis.Model →
  ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
    (U : Type v) [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K Rudvalis.Model U),
    Function.Injective τ → τ.IsAbsolutelyIrreducible →
    Module.finrank K U ≤ 36 → Module.finrank K U = 28

/-- Construct a nonzero map satisfying the two literal generator equations.
The assembly proves equivariance for every group element and bijectivity.
The marked carrier comparison can remain explicit during this calculation. -/
def Degree28GeneratorIntertwining : Prop :=
  ∀ (e : Rudvalis.Model ≃* standardGroup),
    (e Rudvalis.a).val = generatorA → (e Rudvalis.b).val = generatorB →
    IsQuasisimple Rudvalis.Model →
    ∀ (V : Type v) [AddCommGroup V] [Module (ZMod 2) V]
      [FiniteDimensional (ZMod 2) V] (σ : Representation (ZMod 2) Rudvalis.Model V),
      Function.Injective σ → σ.IsAbsolutelyIrreducible →
      Module.finrank (ZMod 2) V = 28 →
      ∃ T : V →ₗ[ZMod 2] Space, T ≠ 0 ∧
        (∀ v, T (σ Rudvalis.a v) = generatorA.val (T v)) ∧
        (∀ v, T (σ Rudvalis.b v) = generatorB.val (T v))

end SmallModuleRecognitionInputs
end CFSG.Quasithin.ChapterK.SporadicCatalogue.RudvalisExclusion
