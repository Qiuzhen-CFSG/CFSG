module

public import Stellmacher.Recognition.LyonsU3Four.AmbientDecompositionRealization
public import Stellmacher.Recognition.LyonsU3Four.TableISurvivorDegrees
public import Stellmacher.Recognition.LyonsU3Four.NTwoStrongEmbedding

/-!
# Extracting the character from the Table I numerical witness

A `DegreeTwelveWitness` for an actual ambient decomposition identifies a unique
degree-twelve irreducible character. Galois closure of the principal block makes
that character rational. The witness's weighted-column identity gives Lemma 4(c)
at every nonidentity element of the Sylow center, using involution fusion.

The local-data and N₂ adapters below take an explicit numerical witness producer.
Ambient realization supplies its pattern, degree, order and prime constraints;
canonical classification and the U/V degree forcing must still supply the
producer. No exhaustive Table I classification is asserted here.

Source: R. Lyons, *A Characterization of the Group U₃(4)*, Trans. AMS 164
(1972), Lemma 4(c), pp. 381–382, and the strong-embedding argument, pp. 385–386.
-/

public section
noncomputable section

namespace Stellmacher.Recognition.LyonsU3Four

open Subgroup ModularBlock.PrincipalBlockConstruction
attribute [local instance] Fintype.ofFinite

variable {G : Type*} [Group G] [Finite G]

namespace AmbientGeneralizedDecompositionData

variable {b : PrincipalCongruenceBlockData G} {t z : G}
  {μ : centralizer ({z} : Set G) →* ℂ}
  (a : AmbientGeneralizedDecompositionData b t z μ)

/-- The unique absolute degree twelve in the numerical witness is the actual
positive degree of a rational irreducible character. -/
theorem rational_character_of_degreeTwelveWitness
    (w : DegreeTwelveWitness a.columns (fun j => (a.degree j : ℤ))) :
    ∃ χ : ClassFunction G, IsIrreducibleCharacter χ ∧ χ 1 = 12 ∧
      ∀ g : G, ∃ q : ℚ, χ g = (q : ℂ) := by
  have hdegree : a.degree w.row = 12 := by
    simpa only [Int.natAbs_natCast] using w.abs_degree
  refine ⟨a.character w.row, a.character_irreducible w.row, ?_, ?_⟩
  · rw [a.character_one, hdegree]
    norm_num
  · apply a.character_rational_of_unique_degree w.row
    intro k hk
    apply w.unique k
    simpa only [Int.natAbs_natCast, hk] using hdegree

/-- Extract both actual-character inputs to the strong-embedding argument
from the numerical witness and the actual order constraints. -/
theorem character_and_formula_of_degreeTwelveWitness [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S) (hz : z ∈ centerImage S)
    (ho : a.columns.OrderConstraints (fun j => (a.degree j : ℤ)) (Nat.card G)
      (Nat.card (centralizer ({z} : Set G)))
      (Nat.card (centralizer (centerImage S : Set G))))
    (w : DegreeTwelveWitness a.columns (fun j => (a.degree j : ℤ))) :
    (∃ χ : ClassFunction G, IsIrreducibleCharacter χ ∧ χ 1 = 12 ∧
      ∀ g : G, ∃ q : ℚ, χ g = (q : ℂ)) ∧
    (∀ u ∈ centerImage S, u ≠ 1 →
      Nat.card G * Nat.card (centralizer (centerImage S : Set G)) ^ 2 =
        195 * Nat.card (centralizer ({u} : Set G)) ^ 3) :=
  ⟨a.rational_character_of_degreeTwelveWitness w,
    a.centralizer_formula_of_weight S h hz ho w.weight_identity⟩

end AmbientGeneralizedDecompositionData

/-- The remaining numerical obligation, restricted to actual decompositions.
All three constraint packages are supplied by ambient realization; the pattern
hypotheses are already part of `a`. A producer must prove existence of the
witness from these inputs, without assuming the final character conclusion. -/
@[expose] def AmbientDegreeTwelveWitnessProducer (S : Sylow 2 G) : Prop :=
  ∀ (b : PrincipalCongruenceBlockData G) (t : S), orderOf t = 4 →
    ∀ (μ : centralizer ({(t : G) ^ 2} : Set G) →* ℂ)
      (a : AmbientGeneralizedDecompositionData b (t : G) ((t : G) ^ 2) μ),
      a.columns.DegreeConstraints ⟨b.principal, b.principal_mem⟩
        (fun j => (a.degree j : ℤ)) →
      a.columns.OrderConstraints (fun j => (a.degree j : ℤ)) (Nat.card G)
        (Nat.card (centralizer ({(t : G) ^ 2} : Set G)))
        (Nat.card (centralizer (centerImage S : Set G))) →
      a.columns.PrimeConstraints (fun j => (a.degree j : ℤ)) (Nat.card G) →
      Nonempty (DegreeTwelveWitness a.columns (fun j => (a.degree j : ℤ)))

/-- Realize the actual decomposition from local data, then apply the explicit
numerical producer and extract the character and all centralizer formulas. -/
theorem character_and_formula_of_local_data_and_degreeTwelveWitnessProducer
    [IsSimpleGroup G] (S : Sylow 2 G) (h : SylowStructure S)
    (d : LocalCentralizerData S) (produce : AmbientDegreeTwelveWitnessProducer S) :
    (∃ χ : ClassFunction G, IsIrreducibleCharacter χ ∧ χ 1 = 12 ∧
      ∀ g : G, ∃ q : ℚ, χ g = (q : ℂ)) ∧
    (∀ u ∈ centerImage S, u ≠ 1 →
      Nat.card G * Nat.card (centralizer (centerImage S : Set G)) ^ 2 =
        195 * Nat.card (centralizer ({u} : Set G)) ^ 3) := by
  obtain ⟨b, t, ht, μ, a, hd, ho, hp⟩ := exists_ambient_decomposition S h d
  obtain ⟨w⟩ := produce b t ht μ a hd ho hp
  exact a.character_and_formula_of_degreeTwelveWitness S h
    (orderFour_square_mem_centerImage S h t ht).1 ho w

/-- The N₂ hypothesis supplies local data; the numerical producer remains
the explicit obligation of Table I classification and degree forcing. -/
theorem character_and_formula_of_isNTwoGroup_and_degreeTwelveWitnessProducer
    [IsSimpleGroup G] (hN : IsNTwoGroup G) (S : Sylow 2 G) (h : SylowStructure S)
    (produce : AmbientDegreeTwelveWitnessProducer S) :
    (∃ χ : ClassFunction G, IsIrreducibleCharacter χ ∧ χ 1 = 12 ∧
      ∀ g : G, ∃ q : ℚ, χ g = (q : ℂ)) ∧
    (∀ u ∈ centerImage S, u ≠ 1 →
      Nat.card G * Nat.card (centralizer (centerImage S : Set G)) ^ 2 =
        195 * Nat.card (centralizer ({u} : Set G)) ^ 3) :=
  character_and_formula_of_local_data_and_degreeTwelveWitnessProducer S h
    (localCentralizerData_of_isNTwoGroup hN S h) produce

/-- Feed the extracted actual character and formula to the existing N₂
strong-embedding theorem. -/
theorem centralizer_eq_and_stronglyEmbedded_of_isNTwoGroup_and_degreeTwelveWitnessProducer
    [IsSimpleGroup G] (hN : IsNTwoGroup G) (S : Sylow 2 G) (h : SylowStructure S)
    (produce : AmbientDegreeTwelveWitnessProducer S) :
    (∀ u ∈ centerImage S, u ≠ 1 →
      centralizer ({u} : Set G) = centralizer (centerImage S : Set G)) ∧
    IsStronglyEmbedded (normalizer (centerImage S : Set G)) := by
  obtain ⟨hchar, hformula⟩ :=
    character_and_formula_of_isNTwoGroup_and_degreeTwelveWitnessProducer hN S h produce
  exact centralizer_eq_and_stronglyEmbedded_of_isNTwoGroup_and_character
    hN S h hchar hformula

/-- The same extraction discharges the character input to the N₂
involution-centralizer odd-core theorem. -/
theorem involutionCentralizer_oddCore_eq_bot_of_isNTwoGroup_and_degreeTwelveWitnessProducer
    [IsSimpleGroup G] (hN : IsNTwoGroup G) (S : Sylow 2 G) (h : SylowStructure S)
    (produce : AmbientDegreeTwelveWitnessProducer S)
    {x : G} (hx : orderOf x = 2) :
    pPrimeCore 2 (centralizer ({x} : Set G)) = ⊥ := by
  obtain ⟨hchar, hformula⟩ :=
    character_and_formula_of_isNTwoGroup_and_degreeTwelveWitnessProducer hN S h produce
  exact involutionCentralizer_oddCore_eq_bot_of_isNTwoGroup_and_character
    hN S h hchar hformula hx

end Stellmacher.Recognition.LyonsU3Four
