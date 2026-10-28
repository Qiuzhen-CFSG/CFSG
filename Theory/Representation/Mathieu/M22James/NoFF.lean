module
public import Theory.Representation.Mathieu.M22James.NoFF.Reduction
public import Theory.Representation.Mathieu.M22James.NoFF.Fixer
/-!
# The genuine triple Mathieu module is not an FF module

An inner offender would have order sixteen and fix the full fixed space of the
native involution. The Hermitian pointwise-fixer calculation then forces an
actor of field displacement rank one, contradicting native involution fusion
and rank two. Outer involutions displace six binary dimensions, exceeding the
ambient two-rank bound five, so no ambient offender survives either.
The final theorem transports this unconditional fact through the source's
literal injective actor map and intertwining representation equivalence.
Source: Aschbacher--Smith H.12.1(12), printed pp.394--395.
-/
public section
open Sporadic.Mathieu Representation Representation.BinaryOffender
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Janko4.InvolutionCentralizers.First.QuotientExtension
open Sporadic.Mathieu.M22TripleCover.Unitary
open Representation.SL2FourNatural
namespace Sporadic.Mathieu.M22TripleCover.NoFF
noncomputable section
lemma binaryRepresentation_not_isFFModule : ¬ IsFFModule binaryRepresentation := by
  rintro ⟨A, hA⟩
  obtain ⟨B, hc, hs, hf⟩ := inner_offender_fixed_representative hA
  obtain ⟨a, ha⟩ := subgroup_realizes_rankOne B hs hc hf
  have hr : ((matrixAction a.val : Matrix (Fin 6) (Fin 6) F) - 1).rank = 1 := by
    rw [ha, add_sub_cancel_left, rankOneDisplacement_rank]
  by_cases h1 : a.val = 1
  · rw [h1, map_one, Matrix.GeneralLinearGroup.coe_one, sub_self, Matrix.rank_zero] at hr
    omega
  · have hh := matrixRank_involution a.val (orderOf_eq_prime (hs a) h1)
    omega
lemma binaryAction_not_isFFModule : ¬ IsFFModule Ambient.binaryAction :=
  ambient_not_isFFModule_of_inner binaryRepresentation_not_isFFModule
lemma markedAction_not_isFFModule {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (j : G →* actionGroup) (hj : Function.Injective j)
    (E : Representation.Equiv ρ (Ambient.binaryAction.comp j)) : ¬ IsFFModule ρ := by
  intro h
  apply binaryAction_not_isFFModule
  exact h.map_equivariant ρ Ambient.binaryAction j hj E.toLinearEquiv
    (fun g v => LinearMap.congr_fun (E.isIntertwining' g) v)
end
end Sporadic.Mathieu.M22TripleCover.NoFF
