module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FiveParabolics.ParabolicConstruction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FiveParabolics.SmallerCases
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FiveParabolics.SourceQuotients
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FiveParabolics.DiagramAction

/-!
# The five-dimensional parabolic reduction in 15.3.24

The full earlier alternative 15.3.11(5) and the rank-two hypothesis give
Y₊/O₂(Y₊) ≃ E₉ and Y₊S/O₂(Y₊S) ≃ S₃ × S₃. The actual marked image of
Y₊(S∩L) is solvable with three-part nine. The product quotient forces the
S-action on L/O₂(L) to be inner. This constructs actual maximal parabolics
over Y₊(S∩L), proves that they generate L, and chooses one outside M.
Its join with S inherits the outside-family, Sylow and characteristic-two
conditions. Its marked Levi quotient has no factor of 31. Applying 15.3.22
to a genuine new component witness therefore leaves only PSL₃(2) and PSL₄(2),
which are eliminated by the permitted earlier theorem inputs.

`exclusion_of_earlier` discharges all geometric preparation in
`exclusion_of_preparation`. Its explicit earlier inputs are 15.3.11(1),(5),(6),
15.3.15(3), 15.3.17(2), and the component existence, model alternatives and
L₃/L₄ exclusions uniformly on smaller outside overgroups. The parent assembly
supplies these earlier results, including the independent L₄ exclusion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.24, printed pp.1129–1130 (PDF pp.1146–1147).
-/

@[expose] public section

open Subgroup BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FiveParabolics
variable {G : Type*} [Group G] (d : LocalData G)

/-- The allowed preceding results, applied to the actual smaller outside
overgroups. Component existence supplies the new star action as part of
its genuine witness. The model conclusion is exactly 15.3.22; the two
exclusions are 15.3.23 and the independent four-dimensional case. -/
structure EarlierInputs (I : Subgroup G) : Prop where
  components : ∀ K : Subgroup G, K < I → K ∈ d.Hplus →
    HasCharacteristicTwo K → Chapter1.IsSylowIn 2 d.S K →
    SolvableInvariantControl d K → primeRank 3 d.Yplus = 2 →
    Nonempty (ComponentWitness d K)
  binary_models : ∀ K : Subgroup G, K < I → K ∈ d.Hplus →
    HasCharacteristicTwo K → Chapter1.IsSylowIn 2 d.S K →
    SolvableInvariantControl d K → primeRank 3 d.Yplus = 2 →
    ∀ c : ComponentWitness d K, ∃ n, (n = 3 ∨ n = 4 ∨ n = 5) ∧
      Nonempty ((c.L ⧸ pCore 2 c.L) ≃* Projective n)
  no_three : ∀ K : Subgroup G, K < I → K ∈ d.Hplus →
    HasCharacteristicTwo K → Chapter1.IsSylowIn 2 d.S K →
    SolvableInvariantControl d K → primeRank 3 d.Yplus = 2 →
    ∀ c : ComponentWitness d K, ((c.L ⧸ pCore 2 c.L) ≃* Projective 3) → False
  no_four : ∀ K : Subgroup G, K < I → K ∈ d.Hplus →
    HasCharacteristicTwo K → Chapter1.IsSylowIn 2 d.S K →
    SolvableInvariantControl d K → primeRank 3 d.Yplus = 2 →
    ∀ c : ComponentWitness d K, ((c.L ⧸ pCore 2 c.L) ≃* Projective 4) → False

/-- Conditional assembly of the five-dimensional parabolic contradiction.
The geometric preparation must still be proved from the source hypotheses:
solvability and three-part nine of the base image, and inner action by S.
No outside parabolic or contradiction is assumed. -/
theorem exclusion_of_preparation [Finite G] {I : Subgroup G}
    (hI : I ∈ d.Hplus) (hS : Chapter1.IsSylowIn 2 d.S I)
    (hf : HasCharacteristicTwo I) (hrank : primeRank 3 d.Yplus = 2)
    (hcontrol : SolvableInvariantControl d I)
    (c : ComponentWitness d I) (e : (c.L ⧸ pCore 2 c.L) ≃* Projective 5)
    (hYL : d.Yplus ≤ c.L) (hθ : c.L = theta I)
    (hsol : Group.IsSolvable (baseImage d e))
    (h3 : (Nat.card (baseImage d e)).factorization 3 = 2)
    (hi : IsInnerOnModel e d.S
      ((Chapter1.isSylowIn_iff.mp hS).2.1.trans (normalizes_of_eq_theta hθ)))
    (earlier : EarlierInputs d I) : False := by
  obtain ⟨b, i, hbase, hout, hn⟩ :=
    exists_outside_parabolic d c e hS hYL hθ hsol h3 hi
  let P := parabolic e b i
  let K := P ⊔ d.S
  have hPL : P ≤ c.L := lift_le e _
  have hSI : d.S ≤ I := (Chapter1.isSylowIn_iff.mp hS).2.1
  have hKI : K ≤ I := sup_le (hPL.trans (component_le c)) hSI
  have hYK : d.Yplus ⊔ d.S ≤ K :=
    sup_le_sup_right (le_sup_left.trans hbase) _
  have hKM : ¬ K ≤ d.M := fun h => hout (le_sup_left.trans h)
  obtain ⟨hK, hSK, hfK⟩ := intermediate_outside d hI hS hf hKI hYK hKM
  have hcontrolK := solvableInvariantControl_restrict d hKI hcontrol
  have h31 : ¬ 31 ∣ Nat.card K := not_thirtyOne_dvd_join P d.S hn
    (Chapter1.isSylowIn_iff.mp hS).1 (parabolic_quotient_models e b i)
  have hKI' : K < I := lt_of_le_of_ne hKI (fun he =>
    component_not_five d c (he ▸ h31) e)
  obtain ⟨cK⟩ := earlier.components K hKI' hK hfK hSK hcontrolK hrank
  have hc := smaller_component_models d cK h31
    (earlier.binary_models K hKI' hK hfK hSK hcontrolK hrank cK)
  rcases hc with hthree | hfour
  · obtain ⟨f⟩ := hthree
    exact earlier.no_three K hKI' hK hfK hSK hcontrolK hrank cK f
  · obtain ⟨f⟩ := hfour
    exact earlier.no_four K hKI' hK hfK hSK hcontrolK hrank cK f

/-- The five-dimensional case of 15.3.24 from the permitted earlier results.
The full 15.3.11(5) alternative is retained: the rank hypothesis selects its
first branch, and the actual PSL₅(2) model excludes the extraspecial quotient.
Both source quotients, the solvable base image and its three-part, and the
inner diagram action are proved before applying the parabolic reduction.
The smaller overgroups use their own component witnesses and star actions. -/
theorem exclusion_of_earlier [Finite G] {I : Subgroup G}
    (hI : I ∈ d.Hplus) (hS : Chapter1.IsSylowIn 2 d.S I)
    (hf : HasCharacteristicTwo I) (hrank : primeRank 3 d.Yplus = 2)
    (hcontrol : SolvableInvariantControl d I)
    (c : ComponentWitness d I) (e : (c.L ⧸ pCore 2 c.L) ≃* Projective 5)
    (hYL : d.Yplus ≤ c.L) (hθ : c.L = theta I)
    (hθM : theta (d.MI I) = d.Yplus)
    (hcases : OutsideStructure.RankTwoCase d I ∨ OutsideStructure.RankOneCase d I)
    (earlier : EarlierInputs d I) : False := by
  obtain ⟨_, hH, hsol, h3⟩ :=
    SourceQuotients.source_preparation_of_earlier d c e hS hYL hθM hrank hcases
  have hi := isInnerOnModel_of_product_quotient d c e hS hYL hθ hH hsol h3
  exact exclusion_of_preparation d hI hS hf hrank hcontrol c e hYL hθ
    hsol h3 hi earlier

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FiveParabolics

end
