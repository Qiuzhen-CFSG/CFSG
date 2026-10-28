module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.PairQuotients
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.SmallFrattini
public import Theory.GroupTheory.FrattiniFlagOddSquares
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.Flag.Sylow

/-!
# Exclusion of the actual PSU₅(4) normalizer component

The intrinsic Frattini flag of a Sylow two-subgroup has two sections of
order sixteen. Their automorphism orders avoid the square of every odd
prime other than three, and their common kernel is solvable. Burnside's
theorem supplies such a prime dividing the original perfect component.
The original pair therefore acts innerly on the full normal component.
Covering uniqueness places the pair in it, and the existing two-local
odd-rank obstruction excludes this actual unitary-five model.

No A₅ marking or outer-solvability premise is required. Source:
Aschbacher--Smith 4.4.10--12 and 10.2.3(2), pp.621--623,745.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.UnitaryFive
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04

/-- Every marked PSU₅(4) Sylow has two quotient actions avoiding each odd
prime square other than nine. -/
theorem source_psu5_four_sylow_odd_square_quotients
    {S : Type*} [Group S] [Finite S] (hS : ClassicalGroup.IsPSU S 5 4)
    (P : Sylow 2 S) {ℓ : ℕ} (hℓ : ℓ.Prime) (ho : Odd ℓ) (h3 : ℓ ≠ 3) :
    HasSolvableQuotientPair (ℓ ^ 2) (MulAut P) := by
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := hS
  let : CharP F 2 := charP_two_of_card_sixteen hcard
  obtain ⟨f⟩ := projective_equiv_identity_four J hcard hconj
  obtain ⟨Q, hQ, hQcard, hquot⟩ := Flag.sylow_invariant_frattini_flag_four
    (HermitianForm.IdentityGram.identityGram J) hcard hconj rfl (e.trans f) P
  exact hasSolvableQuotientPair_square_of_invariant_frattini_flag
    P.isPGroup' Q hQ hQcard hquot hℓ ho h3

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The original odd actor cannot have an escaping normal PSU₅(4) component. -/
theorem source_nonnormal_oddNormalizer_no_unitary_five_component
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K) [K.Normal]
    (hout : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hm : ClassicalGroup.IsPSU (K ⧸ center K) 5 4) : False := by
  let : IsQuasisimple K := hK.2
  let R := L ⧸ pCore 2 L
  let := D.quasisimple
  let : IsSimpleGroup (R ⧸ center R) := IsQuasisimple.simple
  let : Nontrivial R := (QuotientGroup.mk'_surjective (center R)).nontrivial
  obtain ⟨ℓ, hℓ, hoℓ, h3, hd⟩ := Perfect.exists_odd_prime_ne_dvd_card R Nat.prime_three
  let P : Sylow 2 (K ⧸ center K) := Classical.choice inferInstance
  obtain ⟨A, C, hA, hC, hAC, hAi, hCi⟩ :=
    source_psu5_four_sylow_odd_square_quotients hm P hℓ hoℓ h3
  let := hA
  let := hC
  have hinner := source_nonnormal_oddNormalizer_inner_of_sylow_quotients
    D ℓ hd hn hp B hB hBC hperm K P A C hAC hAi hCi
  have ho : Odd (Nat.card B) := by
    obtain ⟨n, he⟩ := hB.exists_card_eq
    rw [he]
    exact hp.pow
  have hu := source_nonnormal_oddPrimeActor_covering_uniqueness D hn hp B hB hBC hBV hperm
  have hFK := (source_nonnormal_oddNormalizer_component_closure_of_overlap_normalizes
    D hn B hBC ho hBV hu K hK hout (le_trans le_top le_normalizer_of_normal) hinner).2.2.2
  exact source_nonnormal_oddNormalizer_no_placed_unitary_five_component
    D hn B hBC ho hBV K hFK hm

end CFSG.Quasithin.Chapter10
