module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.AxisExclusions.Basic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment.Dual

/-!
# Orienting the kernel of a two-factor extension

The actual contragredient automorphism of GL₄(2) exchanges its natural and
contragredient modules. We transport both factors through this one actor
identification. Thus the published two-factor splitting premise applies
also when the kernel is dual in the initially chosen coordinates.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, B.4.9(1), printed p.92, and its application in
13.8.25, printed p.961. The splitting theorem itself remains an explicit
premise; this module proves its change of orientation.
-/

@[expose] public section

universe u v

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.AxisExclusions.TwoStep

open Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors

variable {H : Type u} {U : Type v} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

/-- Changing the actual GL₄(2) identification by the contragredient preserves
natural-or-dual modules, with explicit intertwining equivalences. -/
theorem naturalOrDual_reorient (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* BinaryLinear.GL NaturalSpace) (h : IsNaturalOrDual ρ eH) :
    IsNaturalOrDual ρ (eH.trans Alignment.dualActor) := by
  rcases h with ⟨e, he⟩ | ⟨e, he⟩
  · have hd := Alignment.dual_is_natural ρ.dual eH e.symm.dualMap
      (equivariant_dual ρ (naturalAction eH) e he)
    exact naturalOrDual_of_equivariant ρ ρ.dual.dual
      (Module.evalEquiv (ZMod 2) U) (equivariant_eval ρ) _
      (naturalOrDual_dual ρ.dual _ (Or.inl hd))
  · exact Or.inl (Alignment.dual_is_natural ρ eH e he)

/-- The two-factor premise also applies when the kernel is dual in the
original coordinates: change the actor identification on both factors. -/
theorem complement_of_naturalOrDual_kernel (ρ : Representation (ZMod 2) H U)
    (hsplit : TwoFactorSplitting.{u, v} H)
    (eH : H ≃* BinaryLinear.GL NaturalSpace) (K : Subrepresentation ρ)
    (hfaith : Function.Injective ρ) (hK : IsNaturalOrDual K.toRepresentation eH)
    (hQ : IsNaturalOrDual K.quotientRepresentation eH)
    (E : Subgroup H) (hE : Nat.card E = 4) (hq : IsQuadratic ρ E)
    (ha : HasCommonAxis K.quotientRepresentation E) :
    ∃ D : Subrepresentation ρ, K ⊓ D = ⊥ ∧ K ⊔ D = ⊤ := by
  rcases hK with hK | ⟨e, he⟩
  · exact hsplit U ρ eH K hfaith hK hQ E hE hq ha
  · exact hsplit U ρ (eH.trans Alignment.dualActor) K hfaith
      (Alignment.dual_is_natural K.toRepresentation eH e he)
      (naturalOrDual_reorient K.quotientRepresentation eH hQ) E hE hq ha

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.AxisExclusions.TwoStep
