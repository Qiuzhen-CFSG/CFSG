module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic.CoreComparison.Section

/-!
# The source core-comparison estimate

The original commutator pairing constructs the faithful dual action on
Q_H/H_C. Its line-centralizer image cannot be fixed by the rank-two actor.
The group-theoretic transfer then puts a noncentral commutator in the
literal Dγ, proving Dγ≰H_C. No core representation or moved vector is an
input. The earlier plus-kernel equality is precisely 13.7.4(1).

Source: Aschbacher–Smith 13.8.27, printed p.963. The independent earlier
source inputs remain with qt-d-138-six-g2-source; parabolic marking remains
with this local estimate family.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic
open AlternatingAndLinear.FourStructure.CriticalTransfer CriticalGeometry

variable {G W : Type*} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W]
  {L T H V V₃ V₁ K : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The actual pairing and its earlier faithful kernel force Dγ outside H_C. -/
theorem source_Dgamma_not_le_of_pairing
    (c : CriticalPair L T H V)
    (ρ : Representation (ZMod 2) (Source.Hstar H) W)
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hfaith : Function.Injective ρ) (hUg : c.Ugamma V₃ ≤ H)
    (hH : H = centralizer (V₁ : Set G))
    (hcard : Nat.card V₁ = 2) (hUQ : Source.UH H V₃ ≤ Source.QH H)
    (hAone : c.Aone V₁ ≤ Source.UH H V₃)
    (hcomm : ⁅Source.QH H, Source.UH H V₃⁆ ≤ V₁)
    (hcentralizer : commutatorPreimage H (Source.UH H V₃) V₁ ≤ Source.QH H)
    (hpluskernel : commutatorPreimage H (Source.UH H V₃)
      (Source.UH H V₃ ⊓ centralizer (Source.QH H : Set G)) = Source.QH H)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hfit : generalizedFitting (Source.Hstar H) = Source.starImage H K)
    (eK : (K ⧸ pCore 2 K) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hA : IsElementaryTwo (Source.starImage H (c.Ugamma V₃)))
    (hrank : rank (Source.starImage H (c.Ugamma V₃)) = 2) :
    ¬ Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ ≤ Source.HC H V₃ := by
  obtain ⟨σ, _, tQ, _, hdual, _, _⟩ := source_faithful_core_section
    s.le s.line_le hcard s.centralizes hUQ hcomm hcentralizer hpluskernel
  apply source_Dgamma_not_le_of_core_movement c s hfaith hUg hH σ.dual tQ
  exact core_movement_of_faithful_comparison c ρ s hcard hUQ hAone hcomm
    hKH hK hfit eK hA hrank σ.dual hdual tQ

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic
