module
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.OrbitClosure.SourceSetup
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceModels

/-!
# The original component-orbit input for 15.3.49

The proved 1.2.1(3) theorem applies to the actual component modulo the
ambient two-core. When this core is trivial, the intrinsic component core
is also trivial. Canonical quotient equivalences give exactly the orbit
alternative consumed by the extraspecial reduction, for the full catalogue.

Source: Aschbacher--Smith, 1.2.1(3) and 15.3.49(l), combined manuscript
(1 March 2004), printed pp.504 and 1144.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.OrbitClosure
universe u

/-- The actual 1.2.1(3) source supplies the orbit alternative used in 15.3.49. -/
theorem earlierOrbitAlternative_knownSimple :
    EarlierOrbitAlternative.{u} KnownSimple.IsKnownSimple := by
  intro X _ _ hX hcore B hB
  have hQ : IsSQTK KnownSimple.IsKnownSimple (X ⧸ pCore 2 X) := by
    let e : (X ⧸ pCore 2 X) ≃* X :=
      (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
    exact (IsSQTK.equiv e).mpr hX
  rcases Chapter1.Section02.proposition_1_2_1_three_index_knownSimple hQ hB with
    hn | ⟨hi, hm⟩
  · exact Or.inl hn
  · have hBcore : pCore 2 B = ⊥ := by
      rw [pCore_subnormal_eq_comap 2 hB.subnormal, hcore]
      rw [MonoidHom.comap_bot, B.subtype.ker_eq_bot B.subtype_injective]
    let e : (B ⧸ pCore 2 B) ≃* B :=
      (QuotientGroup.quotientMulEquivOfEq hBcore).trans QuotientGroup.quotientBot
    exact Or.inr ⟨hi, hm.of_mulEquiv e.symm⟩

variable {G : Type u} [Group G] [Finite G]
variable {H M Y L T ZS Z A : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]

/-- Literal consumer at the local section action and its actual component. -/
theorem SourceSetup.nonnormal_alternative_knownSimple
    (d : SourceSetup KnownSimple.IsKnownSimple H M Y L T ZS Z A)
    (hne : localSpan L T ≠ L) :
    (normalizer (L.subgroupOf H : Set H)).index = 2 ∧
      Chapter1.Section02.NonnormalCComponentModel (L ⧸ pCore 2 L) :=
  d.nonnormal_alternative earlierOrbitAlternative_knownSimple hne

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.OrbitClosure
