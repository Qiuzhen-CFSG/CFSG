module
public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.Chapter3.Section02.MinimalModuleSelection
public import Theory.Representation.BinaryConjugationSection.ActionKernel
public import Theory.Representation.OrthogonalFourPlusMatrix.Displacement

/-!
# The literal chosen A₅ tensor branch

The two-factor determinant model retains the original full module, its
minimal source choice, the actual quotient map from L₀, and the original
A₅ marking on the first factor. Coordinates are a conjugation section of
the literal ambient subgroup with trivial kernel, rather than an unrelated
representation. This is the contract shared by tensor recognition and the
specialized Chapter 9 exclusion.

Source: Aschbacher–Smith 3.2.6(1), 9.1, and 10.1, printed pp.581,729,741.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

@[expose] def sourceA5TensorAction
    (q : (localOrbit T L) →* ClassicalOrthogonal.FourPlusMatrix.Binary.G) :
    Representation (ZMod 2) (localOrbit T L) ClassicalOrthogonal.FourPlusMatrix.Binary.V :=
  ClassicalOrthogonal.FourPlusMatrix.Binary.action.comp q

section
attribute [local irreducible] sourceA5TensorAction

/-- The exact eight-dimensional determinant branch for the chosen setup. -/
structure SourceA5TensorModel
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) where
  minimal : D.IsMinimalFullModule
  seed_eq : D.seed = D.fullModule
  module_eq : D.moduleSubgroup = D.fullModule
  quotient : (localOrbit T L) →* ClassicalOrthogonal.FourPlusMatrix.Binary.G
  onto : Function.Surjective quotient
  kernel_eq : quotient.ker = pCore 2 (localOrbit T L)
  firstMarking : alternatingGroup (Fin 5) ≃*
    Matrix.SpecialLinearGroup (Fin 2) ClassicalOrthogonal.FourPlusMatrix.Binary.F
  first_factor (l : L) :
    quotient ⟨l,le_componentOrbit L T l.property⟩ =
      (firstMarking (e (QuotientGroup.mk' (pCore 2 L) l)),1)
  sectionData : BinaryConjugationSection (localOrbit T L) D.fullModule ⊥
    (sourceA5TensorAction quotient)

end

namespace SourceA5TensorModel
variable {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The coordinate map is injective on the original full module. -/
theorem coordinates_injective : Function.Injective m.sectionData.coordinates := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [m.sectionData.kernel_eq,bot_subgroupOf]

include m in
/-- The original full module, not merely an abstract model, has order 256. -/
theorem card_fullModule : Nat.card D.fullModule = 256 := by
  have hc := m.sectionData.card_section
  rw [Subgroup.card_bot,mul_one] at hc
  rw [hc]
  have hd := Module.natCard_eq_pow_finrank
    (K := ZMod 2) (V := ClassicalOrthogonal.FourPlusMatrix.Binary.V)
  simp only [Nat.card_eq_fintype_card,ZMod.card,
    ClassicalOrthogonal.FourPlusMatrix.Binary.finrank_binary] at hd ⊢
  exact hd

end SourceA5TensorModel
end CFSG.Quasithin.Chapter10
