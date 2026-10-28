module

public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.Geometry
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# Source cuts in the local Cartan centralization argument

The contradiction in 5.1.13 first enlarges the witnessed component to a
maximal local component. Thompson movement and the FF classification then
leave an actual A₇ quotient, acting irreducibly on the four- or six-dimensional
commutator of the omega-span. The second argument eliminates this configuration
by comparing the two Thompson actions and using blocks and torus inversion.
After centralization, the final paragraph identifies the entire original
commutator module. These are three separate proof obligations, not assumptions
of the original theorem or inhabited classification certificates.

The subgroup U below is fixed by its definition. Neither its action nor the
selected reduced module W is replaced by arbitrary coordinates.

Source: Aschbacher--Smith, 5.1.13, printed pp.637--638.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The literal commutator U = [⟨Z^K⟩,K] in the centralization contradiction. -/
abbrev localOmegaModule (T : Sylow 2 G) (K : Subgroup G) : Subgroup G :=
  ⁅conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) K, K⁆

/-- The intermediate configuration reached before the two module alternatives
and block argument. Irreducibility is stated on actual invariant subgroups. -/
structure LocalA7Configuration (T : Sylow 2 G) (L H X K : Subgroup G) : Prop where
  contains : X ≤ K
  maximal : K ∈ Chapter1.LStar G (T : Subgroup G)
  sylow_normalizes : (T : Subgroup G) ≤ normalizer (K : Set G)
  quotient : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
  actor_thompson : ⁅K, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ = K
  left_thompson : ⁅L, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ = L
  reduced : localOmegaModule T K ∈ reducedFamily (K ⊔ (T : Subgroup G))
  card : Nat.card (localOmegaModule T K) = 2 ^ 4 ∨
    Nat.card (localOmegaModule T K) = 2 ^ 6
  irreducible : ∀ E : Subgroup G, E ≤ localOmegaModule T K →
    K ≤ normalizer (E : Set G) → E = ⊥ ∨ E = localOmegaModule T K
  span_eq : conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) K =
    localOmegaModule T K ⊔
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (K : Set G))
  fixed_eq_bot : localOmegaModule T K ⊓ centralizer (K : Set G) = ⊥
  residual_moves : ⁅Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓
    localOmegaModule T K, residual H⁆ ≠ ⊥

/-- Maximal enlargement and the FF exclusions, through the four/six-dimensional
A₇ configuration on p.637. The witness producer is not an input. -/
def LocalCartanFFReduction (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (T : Sylow 2 G) (L W : Subgroup G) (n : ℕ),
    Input KnownSimple.IsKnownSimple T L W n →
    ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      1 < ChapterE.generationParameter H →
      ∀ A B : Subgroup G, CartanPair T L H A B →
        ∀ Y ∈ Chapter1.HOver G (H : Set G),
          ∀ X D : Subgroup G, LocalCartanWitness T H A Y X D →
            ¬ X ≤ omegaCentralizer T →
            ∃ K : Subgroup G, LocalA7Configuration T L H X K

/-- The two A₇ module alternatives, block argument, and torus contradiction.
The FF reduction can be proved independently of this conditional implication. -/
def LocalCartanA7Exclusion (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (T : Sylow 2 G) (L W : Subgroup G) (n : ℕ),
    Input KnownSimple.IsKnownSimple T L W n →
    ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      1 < ChapterE.generationParameter H →
      ∀ A B : Subgroup G, CartanPair T L H A B →
        ∀ Y ∈ Chapter1.HOver G (H : Set G),
          ∀ X D : Subgroup G, LocalCartanWitness T H A Y X D →
            ∀ K : Subgroup G, LocalA7Configuration T L H X K → False

/-- The final module argument, with centralization explicit. It must prove
the whole commutator action, including splitting and multiplicity. -/
def LocalCartanModuleRecognition (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (T : Sylow 2 G) (L W : Subgroup G) (n : ℕ),
    Input KnownSimple.IsKnownSimple T L W n →
    ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      1 < ChapterE.generationParameter H →
      ∀ A B : Subgroup G, CartanPair T L H A B →
        ∀ Y ∈ Chapter1.HOver G (H : Set G),
          ∀ X D : Subgroup G, LocalCartanWitness T H A Y X D →
            X ≤ omegaCentralizer T → IsOneOrTwoA5Modules L (layer L W)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
