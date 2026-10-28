module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.FourActors.LocalMember
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.Reduction

/-!
# Centralizer and odd-subgroup controls for the original outer family

The positioned four-group has a genuine rank-one E-member C_G(z)^∞T. If no
family member escapes M, this subgroup is in M. Solvable-quotient lifting
recovers the whole centralizer. Solvable Sylow overgroups and odd subgroups
normalized by C_T(B), for every original family actor B, give further controls.
All intrinsic Sylow, quotient and inheritance premises of those controls are
proved in the imported general finite-group arguments.

The remaining `FourActorCentralizerGeneration` statement is concrete model
geometry with no E-membership premise. Its producer can use any genuine
family member or conjugate. This module does not assert that the centralizer
is maximal in the inner subgroup: in PSL₃ it lies in parabolics.

Source: Aschbacher--Smith E.1.8, E.1.10, E.1.13 and E.1.14(7), printed
pp.211--214; the last refers to Aschbacher, GF(2)-representations of finite
groups (1982), Lemma 4.11.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies
variable (F : Type*) [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]

/-- The remaining matrix-generation statement. It is independent of the
local E-member construction, with all local controls stated literally. -/
@[expose] def FourActorCentralizerGeneration : Prop :=
  ∀ (T : Sylow 2 (graphExtension F)) (Ω : Set (Subgroup (graphExtension F))),
    IsElementaryFamily Ω → LargeActors F T Ω → ¬ HasInnerActor F T Ω →
    ∀ A ∈ Ω, A ≤ (T : Subgroup _) → Nat.card A = 4 →
    Nat.card (A ⊓ innerPart F : Subgroup _) = 2 →
    ∀ z : graphExtension F, orderOf z = 2 → z ∈ innerPart F → z ∈ A →
    (T : Subgroup _) ≤ centralizer ({z} : Set _) →
    ∀ M : Subgroup (graphExtension F),
    centralizer ({z} : Set _) ≤ M →
    normalizer (weakClosure (T : Subgroup _) Ω : Set (graphExtension F)) ≤ M →
    (∀ H : Subgroup (graphExtension F), (T : Subgroup _) ≤ H →
      Group.IsSolvable H → H ≤ M) →
    (∀ B ∈ Ω, B ≤ (T : Subgroup _) →
      ∀ r : ℕ, r.Prime → Odd r → ∀ X : Subgroup (graphExtension F), IsPGroup r X →
      (T : Subgroup _) ⊓ centralizer (B : Set (graphExtension F)) ≤
        normalizer (X : Set (graphExtension F)) → ⁅X, B⁆ ≤ M) → M = ⊤

private def obstructionOfNoEscape {T : Sylow 2 (graphExtension F)}
    {Ω : Set (Subgroup (graphExtension F))} (hΩ : IsElementaryFamily Ω)
    (hlarge : LargeActors F T Ω) {A : Subgroup (graphExtension F)}
    (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup _)) (hfour : Nat.card A = 4)
    {M : Subgroup (graphExtension F)} (hTM : (T : Subgroup _) ≤ M) (hproper : M ≠ ⊤)
    (hNM : normalizer (weakClosure (T : Subgroup _) Ω : Set (graphExtension F)) ≤ M)
    (hnot : ¬ FamilyEscapes F T Ω M) : PSUThreeGeneration.LargeFamilyObstruction T where
  family := Ω
  elementary := hΩ
  overgroup := M
  proper := hproper
  sylow_le := hTM
  normalizer_le := hNM
  large := hlarge
  nontrivial_member := ⟨A, hA, hAT, by
    intro h
    have hc := (eq_bot_iff_card A).mp h
    omega⟩
  members_le := by
    intro B hB hBT K hK
    by_contra hKM
    exact hnot ⟨B, hB, hBT, K, hK, hKM⟩

/-- Failure of escape supplies the full centralizer, solvable-overgroup and
odd-commutator controls for the original family. No extra model premise remains. -/
theorem positioned_four_controls_of_no_escape {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hl : 3 < p) (hF : Nat.card F = p)
    {T : Sylow 2 (graphExtension F)} {Ω : Set (Subgroup (graphExtension F))}
    (hΩ : IsElementaryFamily Ω) (hlarge : LargeActors F T Ω)
    {A : Subgroup (graphExtension F)} (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup _))
    (hfour : Nat.card A = 4) (hinner : Nat.card (A ⊓ innerPart F : Subgroup _) = 2)
    {z : graphExtension F} (hz : orderOf z = 2) (hzL : z ∈ innerPart F) (hzA : z ∈ A)
    (hTz : (T : Subgroup _) ≤ centralizer ({z} : Set _))
    {M : Subgroup (graphExtension F)} (hTM : (T : Subgroup _) ≤ M) (hproper : M ≠ ⊤)
    (hNM : normalizer (weakClosure (T : Subgroup _) Ω : Set (graphExtension F)) ≤ M)
    (hnot : ¬ FamilyEscapes F T Ω M) :
    centralizer ({z} : Set _) ≤ M ∧
      (∀ H : Subgroup (graphExtension F), (T : Subgroup _) ≤ H →
        Group.IsSolvable H → H ≤ M) ∧
      (∀ B ∈ Ω, B ≤ (T : Subgroup _) →
        ∀ r : ℕ, r.Prime → Odd r → ∀ X : Subgroup (graphExtension F), IsPGroup r X →
        (T : Subgroup _) ⊓ centralizer (B : Set (graphExtension F)) ≤
          normalizer (X : Set (graphExtension F)) → ⁅X, B⁆ ≤ M) := by
  let d := obstructionOfNoEscape F hΩ hlarge hA hAT hfour hTM hproper hNM hnot
  have hmember := FourActors.positioned_four_centralizer_isEMemberAt F hp ho hl hF
    T A (hΩ.1 A hA) hAT hfour hinner z hz hzL hzA hTz
  have hKM : innerCentralizerSupplement F T z ≤ M := d.members_le A hA hAT _ hmember
  refine ⟨PSUThreeGeneration.sylow_overgroup_le_of_solvable_quotient d
    (centralizer ({z} : Set _)) hTz (solvableResidual _) (le_sup_left.trans hKM), ?_, ?_⟩
  · intro H hTH hs
    let := hs
    exact PSUThreeGeneration.solvable_sylow_overgroup_le d H hTH
  · intro B hB hBT r hr hodd X hX hn
    let : Fact r.Prime := ⟨hr⟩
    have htau : tau (T : Subgroup _) B ≤ (T : Subgroup _) ⊓
        centralizer (B : Set (graphExtension F)) := by
      intro t ht
      refine ⟨tau_le _ _ ht, mem_centralizer_iff.mpr ?_⟩
      intro b hb
      have hc := (mem_centralizerModulo_iff.mp ht).2 b hb
      rw [twoCore_eq_bot F, mem_bot] at hc
      exact commutatorElement_eq_one_iff_mul_comm.mp hc
    exact PSUThreeGeneration.InnerGeometry.tau_normalized_odd_commutator_le d hB hBT
      (fun he => hodd.not_two_dvd_nat (he ▸ dvd_rfl)) X hX (htau.trans hn)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies
