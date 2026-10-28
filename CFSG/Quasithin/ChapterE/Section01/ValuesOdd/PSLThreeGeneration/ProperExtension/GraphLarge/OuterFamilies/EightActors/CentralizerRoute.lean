module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.OddLocals
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors.FamilyTransport
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors.CentralizerContainment.QuotientTransport

/-!
# Independent inputs for the eight-actor centralizer route

Generation for the restriction of the original family to C_G(z) forces that
centralizer into any obstruction overgroup. The intrinsic Sylow is the original
Sylow restricted to C_G(z), and E.1.8 transports genuine local E-members.
Failure of escape also traps every solvable Sylow overgroup and every odd
commutator normalized by ambient tau. A separate matrix generation calculation
can use these three controls to finish the argument.

Both model inputs below remain explicit. In particular no rank-one generation
claim for the centralizer at p = 5 is asserted: its PSL₂(5) section is outside
the q > 5 scope of E.1.14(6). The final order-eight theorem must also discharge
that small-prime branch separately if this route is used.

Source: Aschbacher--Smith E.1.8, E.1.10, E.1.13 and E.1.14(6)--(7),
pp.210--214; Aschbacher (1982), Lemmas 4.10--4.11.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors
variable (F : Type*) [Field F] [Finite F]

/-- Generation for the literal restricted family, with the original eight-actor
still present. This model input is not asserted uniformly in the prime. -/
@[expose] def CentralizerFamilyGeneration : Prop :=
  ∀ (T : Sylow 2 (graphExtension F)) (Ω : Set (Subgroup (graphExtension F))),
    IsElementaryFamily Ω → ∀ A ∈ Ω, A ≤ (T : Subgroup (graphExtension F)) → Nat.card A = 8 →
    Nat.card (A ⊓ innerPart F : Subgroup _) = 4 →
    ∀ z : graphExtension F, orderOf z = 2 → z ∈ innerPart F → z ∈ A →
    (T : Subgroup (graphExtension F)) ≤ centralizer ({z} : Set (graphExtension F)) →
    let C := centralizer ({z} : Set (graphExtension F))
    eFamilySubgroup 1 ((T : Subgroup (graphExtension F)).subgroupOf C)
        (ChiefOrbit.restrictedFamily C Ω) ⊔
      normalizer (weakClosure ((T : Subgroup (graphExtension F)).subgroupOf C)
        (ChiefOrbit.restrictedFamily C Ω) : Set C) = ⊤

/-- Pure group generation from a centralizer and the two controls supplied by
local E-generation. No E-member, escape or whole-group generation conclusion
is assumed in this input. -/
@[expose] def CentralizerGeometry : Prop :=
  ∀ (T : Sylow 2 (graphExtension F)) (Ω : Set (Subgroup (graphExtension F))),
    IsElementaryFamily Ω → LargeActors F T Ω → ¬ HasInnerActor F T Ω →
    ∀ A ∈ Ω, A ≤ (T : Subgroup (graphExtension F)) → Nat.card A = 8 →
    Nat.card (A ⊓ innerPart F : Subgroup _) = 4 →
    ∀ z : graphExtension F, orderOf z = 2 → z ∈ innerPart F → z ∈ A →
    (T : Subgroup (graphExtension F)) ≤ centralizer ({z} : Set (graphExtension F)) →
    ∀ M : Subgroup (graphExtension F), centralizer ({z} : Set (graphExtension F)) ≤ M →
    normalizer (weakClosure (T : Subgroup (graphExtension F)) Ω : Set (graphExtension F)) ≤ M →
    (∀ H : Subgroup (graphExtension F), (T : Subgroup (graphExtension F)) ≤ H →
      Group.IsSolvable H → H ≤ M) →
    (∀ B ∈ Ω, B ≤ (T : Subgroup (graphExtension F)) → ∀ (r : ℕ), r.Prime → Odd r →
      ∀ X : Subgroup (graphExtension F), IsPGroup r X →
      tau (T : Subgroup (graphExtension F)) B ≤ normalizer (X : Set (graphExtension F)) → ⁅X, B⁆ ≤ M) → M = ⊤

private def obstructionOfNoEscape {T : Sylow 2 (graphExtension F)}
    {Ω : Set (Subgroup (graphExtension F))} (hΩ : IsElementaryFamily Ω)
    (hlarge : LargeActors F T Ω) {M : Subgroup (graphExtension F)}
    (hTM : (T : Subgroup (graphExtension F)) ≤ M) (hM : M ≠ ⊤)
    (hN : normalizer (weakClosure (T : Subgroup (graphExtension F)) Ω : Set (graphExtension F)) ≤ M)
    (hnot : ¬ FamilyEscapes F T Ω M) : PSUThreeGeneration.LargeFamilyObstruction T where
  family := Ω
  elementary := hΩ
  overgroup := M
  proper := hM
  sylow_le := hTM
  normalizer_le := hN
  large := hlarge
  nontrivial_member := exists_nontrivial_actor F T Ω M hM hN
  members_le := by
    intro A hA hAT K hK
    by_contra hKM
    exact hnot ⟨A, hA, hAT, K, hK, hKM⟩

/-- Assemble the two independent centralizer inputs using the literal family,
quotient and Sylow conventions. Neither model input is discharged here. -/
theorem familyEscapes_of_centralizer_inputs
    (hlocal : CentralizerFamilyGeneration F) (hgeometry : CentralizerGeometry F)
    (T : Sylow 2 (graphExtension F)) (Ω : Set (Subgroup (graphExtension F)))
    (hΩ : IsElementaryFamily Ω) (hlarge : LargeActors F T Ω)
    (houter : ¬ HasInnerActor F T Ω) (M : Subgroup (graphExtension F))
    (hTM : (T : Subgroup (graphExtension F)) ≤ M) (hM : M ≠ ⊤)
    (hN : normalizer (weakClosure (T : Subgroup (graphExtension F)) Ω : Set (graphExtension F)) ≤ M)
    (A : Subgroup (graphExtension F)) (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup (graphExtension F)))
    (hcard : Nat.card A = 8) (hinner : Nat.card (A ⊓ innerPart F : Subgroup _) = 4)
    (z : graphExtension F) (hz : orderOf z = 2) (hzL : z ∈ innerPart F) (hzA : z ∈ A)
    (hTz : (T : Subgroup (graphExtension F)) ≤ centralizer ({z} : Set (graphExtension F))) : FamilyEscapes F T Ω M := by
  classical
  by_contra hnot
  let d := obstructionOfNoEscape F hΩ hlarge hTM hM hN hnot
  have hCM : centralizer ({z} : Set (graphExtension F)) ≤ M :=
    PSUThreeGeneration.OuterFamilies.EightActors.family_generated_sylow_overgroup_le
      d _ hTz (hlocal T Ω hΩ A hA hAT hcard hinner z hz hzL hzA hTz)
  apply hM
  apply hgeometry T Ω hΩ hlarge houter A hA hAT hcard hinner z hz hzL hzA hTz M hCM hN
  · intro H hTH hs
    let := hs
    exact PSUThreeGeneration.solvable_sylow_overgroup_le d H hTH
  · intro B hB hBT r hr ho X hX hn
    let : Fact r.Prime := ⟨hr⟩
    have hr2 : r ≠ 2 := fun he => ho.not_two_dvd_nat (he ▸ dvd_rfl)
    by_contra hmove
    exact hnot (familyEscapes_of_normalized_odd_commutator F hΩ hB hBT hr2 X hX hn M hmove)

/-- Generation in the literal radical quotient of the residual Sylow
supplement is sufficient. Solvable-kernel lifting recovers the full
centralizer before applying the matrix geometry. -/
theorem familyEscapes_of_residual_quotient_generation
    (hgeometry : CentralizerGeometry F)
    (T : Sylow 2 (graphExtension F)) (Ω : Set (Subgroup (graphExtension F)))
    (hΩ : IsElementaryFamily Ω) (hlarge : LargeActors F T Ω)
    (houter : ¬ HasInnerActor F T Ω) (M : Subgroup (graphExtension F))
    (hTM : (T : Subgroup _) ≤ M) (hM : M ≠ ⊤)
    (hN : normalizer (weakClosure (T : Subgroup _) Ω : Set (graphExtension F)) ≤ M)
    (A : Subgroup (graphExtension F)) (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup _))
    (hcard : Nat.card A = 8) (hinner : Nat.card (A ⊓ innerPart F : Subgroup _) = 4)
    (z : graphExtension F) (hz : orderOf z = 2) (hzL : z ∈ innerPart F) (hzA : z ∈ A)
    (hTz : (T : Subgroup _) ≤ centralizer ({z} : Set _))
    (hgen : let K := PSUThreeGeneration.centralizerResidualOvergroup T z
      IsEGenerated 1 (K ⧸ solvableRadical K)) : FamilyEscapes F T Ω M := by
  classical
  by_contra hnot
  let d := obstructionOfNoEscape F hΩ hlarge hTM hM hN hnot
  let K := PSUThreeGeneration.centralizerResidualOvergroup T z
  let q := QuotientGroup.mk' (solvableRadical K)
  let S := (T.subtype (show (T : Subgroup _) ≤ K from le_sup_right)).mapSurjective
    (f := q) (QuotientGroup.mk'_surjective _)
  have hCM : centralizer ({z} : Set (graphExtension F)) ≤ M :=
    PSUThreeGeneration.OuterFamilies.EightActors.centralizer_le_of_residual_quotient_family_generation
      d hTz (hgen S _ ((ChiefOrbit.restrictedFamily_elementary K hΩ).map q
        (QuotientGroup.mk'_surjective _)))
  apply hM
  apply hgeometry T Ω hΩ hlarge houter A hA hAT hcard hinner z hz hzL hzA hTz M hCM hN
  · intro H hTH hs
    let _ := hs
    exact PSUThreeGeneration.solvable_sylow_overgroup_le d H hTH
  · intro B hB hBT r hr ho X hX hn
    let _ : Fact r.Prime := ⟨hr⟩
    by_contra hmove
    exact hnot (familyEscapes_of_normalized_odd_commutator F hΩ hB hBT
      (fun he => ho.not_two_dvd_nat (he ▸ dvd_rfl)) X hX hn M hmove)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors
