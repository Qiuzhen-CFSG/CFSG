module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Actors
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.Reduction

/-!
# Local inputs for the inner-family graph-extension argument

The four-group calculation discharges the quotient-image rank in E.1.5:
the common central involution lies in the solvable radical of its centralizer
residual supplement. Full ambient Sylow containment discharges E₀. Once the
remaining E2 component conditions are supplied, the entire involution
centralizer lies in the family generation target, by solvable-quotient lifting.

Failure of escape also traps every solvable Sylow overgroup and every odd
commutator normalized by the actual ambient tau. We reuse the general
finite-group lemmas currently housed in the PSU₃ reduction; no unitary model
hypothesis or unitary classification theorem is used here.

The two explicit inputs below separate the component calculation from the
matrix generation geometry. Neither input is asserted here. Their conditional
assembly retains the original family and produces an actual escaping E-member.

Source: Aschbacher--Smith, E.1.2, E.1.5, E.1.8, E.1.10 and E.1.14(7),
printed pp.210--214; Aschbacher, *GF(2)-representations of finite groups*
(1982), Lemma 4.11.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge

variable (F : Type*) [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]

/-- The remaining intrinsic component conditions for C_G(z)^∞ T.
The rank bound and E₀ are deliberately not part of this matrix input. -/
@[expose] def InnerCentralizerStructure : Prop :=
  ∀ (T : Sylow 2 (graphExtension F)) (A : Subgroup (graphExtension F)),
    IsElementaryAbelian 2 A → Nat.card A = 4 → A ≤ (T : Subgroup (graphExtension F)) →
    A ≤ innerPart F → ∀ z : graphExtension F, orderOf z = 2 → z ∈ A →
    (T : Subgroup (graphExtension F)) ≤ centralizer ({z} : Set (graphExtension F)) →
    ECaseComponent (T : Subgroup (graphExtension F)) A (innerCentralizerSupplement F T z)

/-- A matrix-generation input independent of E-membership: the centralizer,
weak-closure normalizer, solvable Sylow overgroups, and odd commutators
controlled by C_T(A), for the original family actors, generate the graph model.
The family remains conjugation invariant, so the geometry may change actors. -/
@[expose] def InnerCentralizerGeneration : Prop :=
  ∀ (T : Sylow 2 (graphExtension F)) (Ω : Set (Subgroup (graphExtension F))),
    IsElementaryFamily Ω → LargeActors F T Ω → HasInnerActor F T Ω →
    ∀ z : graphExtension F, orderOf z = 2 → z ∈ innerPart F →
    (T : Subgroup (graphExtension F)) ≤ centralizer ({z} : Set (graphExtension F)) →
    ∀ M : Subgroup (graphExtension F),
    centralizer ({z} : Set (graphExtension F)) ≤ M →
    normalizer (weakClosure (T : Subgroup (graphExtension F)) Ω : Set (graphExtension F)) ≤ M →
    (∀ H : Subgroup (graphExtension F), (T : Subgroup (graphExtension F)) ≤ H →
      Group.IsSolvable H → H ≤ M) →
    (∀ A ∈ Ω, A ≤ (T : Subgroup (graphExtension F)) →
      ∀ (r : ℕ), r.Prime → Odd r → ∀ X : Subgroup (graphExtension F), IsPGroup r X →
      (T : Subgroup (graphExtension F)) ⊓ centralizer (A : Set (graphExtension F)) ≤
        normalizer (X : Set (graphExtension F)) → ⁅X, A⁆ ≤ M) → M = ⊤

omit [IsSimpleGroup PSL(3,F)] in
/-- A central involution kills one dimension of the actual radical-quotient
image of an inner four-group, giving the required rank-one E2 member. -/
theorem innerCentralizerSupplement_isEMemberAt
    (T : Sylow 2 (graphExtension F)) (A : Subgroup (graphExtension F))
    (hA : IsElementaryAbelian 2 A) (hfour : Nat.card A = 4)
    (hAT : A ≤ (T : Subgroup (graphExtension F))) (z : graphExtension F)
    (hz : orderOf z = 2) (hzA : z ∈ A)
    (hTz : (T : Subgroup (graphExtension F)) ≤ centralizer ({z} : Set (graphExtension F)))
    (hcase : ECaseComponent (T : Subgroup (graphExtension F)) A (innerCentralizerSupplement F T z)) :
    IsEMemberAt 1 (T : Subgroup (graphExtension F)) A (innerCentralizerSupplement F T z) := by
  let K := innerCentralizerSupplement F T z
  have hTK : (T : Subgroup (graphExtension F)) ≤ K := le_sup_right
  have hKz : K ≤ centralizer ({z} : Set (graphExtension F)) := sup_le (map_subtype_le _) hTz
  let w : K := ⟨z, hTK (hAT hzA)⟩
  have hwC : w ∈ center K := by
    rw [mem_center_iff]
    intro k
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hKz k.property))
  let : Group.IsSolvable (center K) := Group.isSolvable_of_comm
    (fun a b => Subtype.ext (mem_center_iff.mp b.property a))
  have hwR : w ∈ solvableRadical K :=
    le_solvableRadical (center K) inferInstance inferInstance hwC
  have hmem : IsEMember (T : Subgroup (graphExtension F)) A K :=
    ⟨hA, hAT, hAT.trans hTK, le_inf (tau_le _ _) ((tau_le _ _).trans hTK),
      ⟨T.subtype hTK, rfl⟩, Or.inr hcase⟩
  apply PSUThreeGeneration.isEMemberAt_one_of_four_radical_element hmem hcase hfour w hzA
    _ hwR
  intro h
  have he : z = 1 := congrArg Subtype.val h
  simp [he] at hz

omit [IsSimpleGroup PSL(3,F)] in
/-- Solvable-quotient lifting recovers the whole centralizer from the E2
residual supplement. This uses its actual intrinsic quotient and inclusion. -/
theorem inner_centralizer_le_generationTarget
    (T : Sylow 2 (graphExtension F)) {Ω : Set (Subgroup (graphExtension F))}
    (hΩ : IsElementaryFamily Ω) {A : Subgroup (graphExtension F)}
    (hA : A ∈ Ω) (hfour : Nat.card A = 4) (hAT : A ≤ (T : Subgroup (graphExtension F)))
    (z : graphExtension F) (hz : orderOf z = 2) (hzA : z ∈ A)
    (hTz : (T : Subgroup (graphExtension F)) ≤ centralizer ({z} : Set (graphExtension F)))
    (hcase : ECaseComponent (T : Subgroup (graphExtension F)) A (innerCentralizerSupplement F T z)) :
    centralizer ({z} : Set (graphExtension F)) ≤ ChiefOrbit.generationTarget 1 T Ω := by
  have hmem := innerCentralizerSupplement_isEMemberAt F T A (hΩ.1 A hA)
    hfour hAT z hz hzA hTz hcase
  have hKE : innerCentralizerSupplement F T z ≤ eFamilySubgroup 1 (T : Subgroup (graphExtension F)) Ω :=
    (show innerCentralizerSupplement F T z ≤ eSubgroup 1 (T : Subgroup (graphExtension F)) A from
      le_sSup hmem).trans
      (le_iSup (fun B : {B : Subgroup (graphExtension F) // B ∈ Ω ∧ B ≤ (T : Subgroup (graphExtension F))} =>
        eSubgroup 1 (T : Subgroup (graphExtension F)) B.1) ⟨A, hA, hAT⟩)
  exact ChiefOrbit.overgroup_le_target_of_solvable_quotient (by decide) T
    (centralizer ({z} : Set (graphExtension F))) hTz hΩ
    (solvableResidual (centralizer ({z} : Set (graphExtension F))))
    (le_sup_left.trans (hKE.trans le_sup_left))

private def obstructionOfNoEscape {T : Sylow 2 (graphExtension F)}
    {Ω : Set (Subgroup (graphExtension F))} (hΩ : IsElementaryFamily Ω)
    (hlarge : LargeActors F T Ω) (hi : HasInnerActor F T Ω)
    {M : Subgroup (graphExtension F)} (hTM : (T : Subgroup (graphExtension F)) ≤ M) (hproper : M ≠ ⊤)
    (hNM : normalizer (weakClosure (T : Subgroup (graphExtension F)) Ω : Set (graphExtension F)) ≤ M)
    (hnot : ¬ FamilyEscapes F T Ω M) : PSUThreeGeneration.LargeFamilyObstruction T where
  family := Ω
  elementary := hΩ
  overgroup := M
  proper := hproper
  sylow_le := hTM
  normalizer_le := hNM
  large := hlarge
  nontrivial_member := by
    obtain ⟨A, hA, hAT, hne, _⟩ := hi
    exact ⟨A, hA, hAT, hne⟩
  members_le := by
    intro A hA hAT K hK
    by_contra hKM
    exact hnot ⟨A, hA, hAT, K, hK, hKM⟩

/-- Conditional assembly of the two independent model calculations. It proves
the literal family escape, including mixed families with outer members.
Both structure and generation inputs must still be supplied by model proofs. -/
theorem familyEscapes_of_inner_centralizer_and_generation {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p)
    (hlocal : InnerCentralizerStructure F) (hgeometry : InnerCentralizerGeneration F)
    (T : Sylow 2 (graphExtension F)) (Ω : Set (Subgroup (graphExtension F)))
    (hΩ : IsElementaryFamily Ω) (hlarge : LargeActors F T Ω) (hi : HasInnerActor F T Ω)
    (M : Subgroup (graphExtension F)) (hTM : (T : Subgroup (graphExtension F)) ≤ M) (hproper : M ≠ ⊤)
    (hNM : normalizer (weakClosure (T : Subgroup (graphExtension F)) Ω : Set (graphExtension F)) ≤ M) :
    FamilyEscapes F T Ω M := by
  classical
  by_contra hnot
  let d := obstructionOfNoEscape F hΩ hlarge hi hTM hproper hNM hnot
  obtain ⟨z, hz, hzI, _, hTz, hall⟩ := exists_common_inner_involution F hp ho hF hΩ hlarge hi
  obtain ⟨A, hA, hAT, hne, hAI⟩ := hi
  have hfour := inner_actor_card_eq_four F hp ho hF hΩ hlarge hA hAT hne hAI
  have hzA := hall A hA hAT hne hAI
  have hCM : centralizer ({z} : Set (graphExtension F)) ≤ M :=
    (inner_centralizer_le_generationTarget F T hΩ hA hfour hAT z hz hzA hTz
      (hlocal T A (hΩ.1 A hA) hfour hAT hAI z hz hzA hTz)).trans
      (PSUThreeGeneration.generationTarget_le_overgroup d)
  apply hproper
  apply hgeometry T Ω hΩ hlarge ⟨A, hA, hAT, hne, hAI⟩ z hz hzI hTz M hCM hNM
  · intro H hTH hs
    let := hs
    exact PSUThreeGeneration.solvable_sylow_overgroup_le d H hTH
  · intro B hB hBT r hr ho X hX hn
    let : Fact r.Prime := ⟨hr⟩
    have hr2 : r ≠ 2 := fun he => ho.not_two_dvd_nat (he ▸ dvd_rfl)
    have htau : tau (T : Subgroup (graphExtension F)) B ≤ (T : Subgroup (graphExtension F)) ⊓ centralizer (B : Set (graphExtension F)) := by
      intro t ht
      refine ⟨tau_le _ _ ht, mem_centralizer_iff.mpr ?_⟩
      intro a ha
      have hc := (mem_centralizerModulo_iff.mp ht).2 a ha
      rw [twoCore_eq_bot F, mem_bot] at hc
      exact commutatorElement_eq_one_iff_mul_comm.mp hc
    exact PSUThreeGeneration.InnerGeometry.tau_normalized_odd_commutator_le d hB hBT
      hr2 X hX (htau.trans hn)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge
