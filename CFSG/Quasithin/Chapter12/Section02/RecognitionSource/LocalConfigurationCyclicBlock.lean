module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicBlockCore
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicBlockRecognition
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicAssembly

/-!
# The linear-block conclusion of original 12.2.24

The cyclic core displacement identifies the original component's commutator
layer with the chosen natural module. Intrinsic recognition supplies every
short-group clause and the equivariant model of its literal block quotient.
The final application discharges blockStep in the existing cyclic assembly.
The earlier natural-action, invariant-odd and prime-order inputs remain
conditional as prescribed; neither self-normalization nor O₂(L)=V is used.
NoEscape and TI need not be used again after these earlier inputs are given.

Source: Aschbacher--Smith, Lemma 12.2.24, printed p.804.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U W : Subgroup G} {d p : ℕ} {g v : G}

/-- Original 12.2.24 under the earlier conditional source inputs. -/
theorem linearTwoBlock_of_cyclic_core_displacement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d)
    (S : InvariantOddLocalAnalysis T L V d p H P U W g v)
    (hc : Nat.card P = p)
    (hd : ⁅(T : Subgroup G) ⊓ centralizer (V : Set G), U⁆ ≤ U ⊓ V) :
    ChapterC.IsLinearTwoBlock L d :=
  linearTwoBlock_of_commutator_eq h D A (cyclic_component_commutator_eq h D structural A S hc hd)


/-- Discharge the exact blockStep in the cyclic assembly. The odd-subgroup
construction and its prime-order proof remain with their original producers. -/
theorem cyclicLocalAnalysis_of_invariant_odd_and_prime_steps
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d)
    (oddStep : ∃ p H P U W g v,
      InvariantOddLocalAnalysis T L V d p H P U W g v)
    (primeStep : ∀ p H P U W g v,
      InvariantOddLocalAnalysis T L V d p H P U W g v → Nat.card P = p) :
    ∃ H P U, CyclicLocalAnalysis T L V d H P U := by
  exact cyclicLocalAnalysis_of_invariant_odd_steps
    (((structural G T L h).2.2 V D).1) oddStep primeStep
    (fun _ _ _ _ _ _ _ S hc hd =>
      linearTwoBlock_of_cyclic_core_displacement h D structural A S hc hd)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
