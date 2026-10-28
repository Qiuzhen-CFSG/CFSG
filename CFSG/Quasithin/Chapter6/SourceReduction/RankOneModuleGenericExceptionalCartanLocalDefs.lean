module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartan

/-!
# The two local arguments preceding Cartan relocation

The first part of 5.1.13 constructs a normal C-component of the original
local overgroup, identifies its actual two-core quotient, and finds an
escaping cubic inside both that component and the original Cartan. The
second part proves omega-centralization and identifies the full moved
module. Neither argument is supplied by these definitions.

The escaping cubic matters: after centralization, it permits a second
application of the first argument in C_G(Ω₁(Z(T))). Merely restricting the
first component to this centralizer would not prove relative subnormality.
The assembly making that second application is in the companion Local
module. Both obligations quantify over the original Sylow and module
choices, as required when 5.2.2 changes the Sylow subgroup.

Source: Aschbacher--Smith, 5.1.12--13, printed pp.635--638.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The output of the embedding sieve, before omega-centralization.
Here X is a component of Y, not a component of G. The subgroup D is the
actual order-three part of the intersected Cartan in the source proof. -/
structure LocalCartanWitness (T : Sylow 2 G) (H A Y X D : Subgroup G) : Prop where
  component_le : X ≤ Y
  component : (X.subgroupOf Y).IsCComponent
  component_normal : (X.subgroupOf Y).Normal
  residual_le : residual H ≤ X
  residual_linear :
    ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4
  component_model :
    Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 7)) ∨
      Nonempty ((X ⧸ pCore 2 X) ≃* Sporadic.LeechRelated.J2.Carrier) ∨
      Nonempty ((X ⧸ pCore 2 X) ≃* Sporadic.Mathieu.M23)
  cubic_le : D ≤ A ⊓ X
  cubic_card : Nat.card D = 3
  cubic_escape : ¬ D ≤ normalizer (residual H : Set G)
  cubic_inverted : ∃ t ∈ (T : Subgroup G) ⊓ X,
    ∀ d ∈ D, t * d * t⁻¹ = d⁻¹

/-- The component sieve of 5.1.12 and the first part of 5.1.13, ending
with the escaping cubic on p.637. Its proof must construct both witnesses. -/
def LocalCartanSieve (κ : GroupClass.{u}) (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (T : Sylow 2 G) (L W : Subgroup G) (n : ℕ), Input κ T L W n →
    ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      1 < ChapterE.generationParameter H →
      ∀ A B : Subgroup G, CartanPair T L H A B →
        ∀ Y ∈ Chapter1.HOver G (H : Set G),
          ¬ A ⊓ Y ≤ normalizer (residual H : Set G) →
          ∃ X D : Subgroup G, LocalCartanWitness T H A Y X D

/-- The remaining local argument on pp.637--638. The previously constructed
component and cubic are explicit inputs; centralization, module coordinates
and the exponent are not assumptions. This can be proved independently of
the producer of `LocalCartanWitness`. -/
def LocalCartanCentralization (κ : GroupClass.{u})
    (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (T : Sylow 2 G) (L W : Subgroup G) (n : ℕ), Input κ T L W n →
    ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      1 < ChapterE.generationParameter H →
      ∀ A B : Subgroup G, CartanPair T L H A B →
        ∀ Y ∈ Chapter1.HOver G (H : Set G),
          ∀ X D : Subgroup G, LocalCartanWitness T H A Y X D →
          X ≤ omegaCentralizer T ∧ IsOneOrTwoA5Modules L (layer L W)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
