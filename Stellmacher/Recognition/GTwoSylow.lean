module
public import Stellmacher.ExceptionalType
public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexModelSetup
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Defs

/-!
# Ambient Sylow order in the local G₂(2)' type

For a finite group with Stellmacher's actual local `G₂(2)'` configuration,
every ambient Sylow two-subgroup has order 32 or 64. Neither simplicity nor
local solvability is required for this consequence of the type data.

Use the second vertex of the configuration. Its actual two-core is a central
product C₄ ∘ Q₈ or Q₈ ∘ Q₈, so the proved central-product counting lemmas give
order 16 or 32. The supplied quotient homomorphism onto SL₂(2), with exactly
that core as kernel, gives vertex order 96 or 192. Its injective embedding in
the ambient group preserves this order. The pair's ambient Sylow intersection
lies in the embedded vertex, hence restricts to a Sylow subgroup there. The
Sylow order formula and ambient Sylow conjugacy give the claimed two values
for the supplied ambient Sylow subgroup.

This proves a direct consequence of (8.6)(a) and the local-type definition
after (8.6), in `refs/latex/stellmacher-n-group.tex` (journal pp. 41, 45).
It uses the actual ambient Sylow intersection and does not transfer the
separate cardinal bounds on the native graph subgroup S. The conclusion is
an order calculation, with global model recognition left to its consumers.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven

private theorem quotient_sl2_card {G : Type*} [Group G] [Finite G]
    (P Q : Subgroup G) (hQP : Q ≤ P) (hmodel : QuotientIsModel P Q SL2Two) :
    Nat.card P = 6 * Nat.card Q := by
  obtain ⟨projection, hsurj, hker⟩ := hmodel
  have hcount := projection.ker.index_mul_card
  rw [Subgroup.index_ker, projection.range_eq_top_of_surjective hsurj,
    Subgroup.card_top, hker] at hcount
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv] at hcount
  have hmodelCard : Nat.card SL2Two = 6 :=
    SectionOne.RankOneThreeGroupAssembly.isSL2Two_card ⟨MulEquiv.refl _⟩
  rw [hmodelCard] at hcount
  exact hcount.symm

/-- The actual local G₂(2)' type bounds every ambient Sylow two-subgroup. -/
public theorem sylow_card_of_gTwoTwoDerived_type
    {G : Type*} [Group G] [Finite G] (S0 : Sylow 2 G)
    (hType : IsOfGTwoTwoDerivedType G) : Nat.card S0 = 32 ∨ Nat.card S0 = 64 := by
  obtain ⟨data⟩ := hType
  let _ := data.groupK
  let _ := data.finiteK
  let P := GAt data.Γ data.criticalPath.firstStep
  let Q := QAt data.Γ data.criticalPath.firstStep
  have hQP : Q ≤ P := by
    change data.Γ.twoCoreAt _ ≤ data.Γ.vertexStabilizer _
    rw [data.Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hQcard : Nat.card Q = 16 ∨ Nat.card Q = 32 := by
    rcases data.caseA.next_twoCore.1 with hsmall | hlarge
    · exact Or.inl (SectionEight.eight_six_c4_quaternion_card hsmall)
    · exact Or.inr (SectionEight.eight_six_quaternion_quaternion_card hlarge)
  have hPcard : Nat.card P = 6 * Nat.card Q :=
    quotient_sl2_card P Q hQP (data.caseA.local_quotients _)
  let mappedP := P.map data.embedding
  have hmapCard : Nat.card mappedP = Nat.card P :=
    Subgroup.card_map_of_injective data.embedding_injective
  have hSylowLe : (data.sylowIntersection : Subgroup G) ≤ mappedP := by
    rw [← data.intersection_eq]
    exact inf_le_right
  let localSylow : Sylow 2 mappedP := data.sylowIntersection.subtype hSylowLe
  have hlocalCard : Nat.card S0 = Nat.card localSylow := by
    exact (Nat.card_congr (S0.equiv data.sylowIntersection).toEquiv).trans
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSylowLe).toEquiv).symm
  rw [hlocalCard, localSylow.card_eq_multiplicity, hmapCard, hPcard]
  rcases hQcard with hsmall | hlarge
  · rw [hsmall]
    left
    change 2 ^ (3 * 2 ^ 5).factorization 2 = 32
    rw [Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow]
    norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
  · rw [hlarge]
    right
    change 2 ^ (3 * 2 ^ 6).factorization 2 = 64
    rw [Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow]
    norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]

end Stellmacher.Recognition
