module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve.ActionTransport
public import Theory.SpecificGroups.SU3.SylowPointwiseInner
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SylowPointwiseInner
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification

/-!
# Unitary, Suzuki and larger symplectic branches of the binary sieve

The literal E* acts as square-one automorphisms fixing an actual Sylow
two-subgroup of the identified component model. Binary PSU₃ Sylow fixers
are inner by the root-coordinate calculation; Suzuki square-one automorphisms
are inner because the full outer group has odd order; nonbinary Sp₄ Sylow
fixers are inner by the proved diagram-preserving semilinear classification.
Faithfulness of the quotient action therefore puts E* inside K*.

The unitary model retains its quadratic matrix field and Hermitian Frobenius.
The symplectic comparison is the actual central quotient map in characteristic
two. The Suzuki defining exponent remains 2*n+1. Unitary simplicity is
transported from K/Z(K), using the given genuine component hypothesis.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the binary
field sieve in the proof of 13.6.6, printed p.927 (PDF p.944), following
the positive alternatives 1.1.5(3)(a,b), printed pp.501–503. These three
branches use only the supplied component, action and exact model identification.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve
open A5Module
variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}
  {s : Marking L V} {T : Sylow 2 G}

/-- The binary unitary-three branch on the genuine component image. -/
theorem largeField_of_unitary_three (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K) {m : ℕ} (hm : 2 ≤ m)
    (hi : ClassicalGroup.IsPSU (NormalizerAction.componentImage K) 3 (2 ^ m)) :
    LargeField K a := by
  refine ⟨m, by omega, .unitary_three m hm hi, ?_⟩
  obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := hi
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := m * 2)
    (by simpa only [Nat.card_eq_fintype_card, pow_mul] using hF)
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 m
    (by omega) hF hconj
  obtain ⟨f⟩ := BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J (2 ^ m) hF hfixed
  let eQ := e.trans f
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : IsSimpleGroup _ :=
    ((NormalizerAction.componentCentralQuotientEquiv K).trans eQ).symm.isSimpleGroup
  apply EStar_le_component_of_model_involutive_fixers K hK a eQ
  intro S α hα hfix
  obtain ⟨b, hb⟩ := BenderSuzuki.MatrixGroups.HermitianForm.SylowPointwiseInner.involutive_fixing_sylow_inner
    (BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J)
    rfl hm hF hconj S α hα hfix
  exact ⟨b, hb.symm⟩

/-- Suzuki's odd outer order places E* in K*, retaining field exponent 2*n+1. -/
theorem largeField_of_suzuki (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K) {n : ℕ} (hn : 1 ≤ n)
    (hi : Nonempty (NormalizerAction.componentImage K ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup n)) : LargeField K a := by
  refine ⟨2 * n + 1, by omega, .suzuki n hn hi, ?_⟩
  obtain ⟨e⟩ := hi
  apply EStar_le_component_of_model_involutive_fixers K hK a e
  intro _ α hα _
  obtain ⟨b, hb⟩ := MulAut.inner_of_sq_eq_one_of_odd_index
    (BenderSuzuki.MatrixGroups.suzuki_odd_outer_index n hn) α hα
  exact ⟨b, hb.symm⟩

/-- Nonbinary symplectic Sylow fixers are inner on the actual PSp₄ carrier. -/
theorem largeField_of_symplectic (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K) {m : ℕ} (hm : 2 ≤ m)
    (hi : ClassicalGroup.IsPSp (NormalizerAction.componentImage K) 2 (2 ^ m)) :
    LargeField K a := by
  refine ⟨m, by omega, .symplectic m hm hi, ?_⟩
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hi
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let eQ := e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm
  apply EStar_le_component_of_model_fixers K hK a eQ
  intro S α hfix
  obtain ⟨b, _, hb⟩ :=
    Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.aut_fixing_sylow_inner
      hF (by omega)
      Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.inner_field_of_preservesDiagram
      S α hfix
  exact ⟨b, hb.symm⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve
