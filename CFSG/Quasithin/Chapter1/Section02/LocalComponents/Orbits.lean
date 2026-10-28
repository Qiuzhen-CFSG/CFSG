module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients
public import CFSG.Quasithin.ClassicalModels
public import BenderSuzuki.MatrixGroups.Suzuki
public import Theory.SpecificGroups.Janko1.Model.Basic

/-!
# Conjugacy orbits and normality of local C-components

Proposition 1.2.1(3) follows from A.3.8(3) by the equivariant solvable-quotient
correspondence and the actual isomorphism from the intrinsic two-core quotient
to the quotient image. Every model alternative below contains a multiplicative
equivalence to the specified matrix or Janko construction.

For the normality assertion of 1.2.4, uniqueness makes the Sylow subgroup
normalize the containing C-component. Its normalizer consequently has odd
index, ruling out the orbit of length two. This proves containment and
normality, but not the additional A.3.12 embedding-list assertion.

The earlier results and the SQTK hypothesis on the quotient are explicit inputs.
Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined 1 March 2004 manuscript, pp. 504–505.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter1.Section02
universe u v

/-- The complete four-model list in Proposition 1.2.1(3), with actual isomorphisms. -/
inductive NonnormalCComponentModel (G : Type u) [Group G] : Prop
  | linear_even (n : ℕ) (hn : 2 ≤ n) (iso : ClassicalGroup.IsPSL G 2 (2 ^ n))
  | suzuki (m : ℕ) (hm : 1 ≤ m)
      (iso : Nonempty (G ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))
  | linear_prime (p : ℕ) (hp : p.Prime) (hodd : Odd p)
      (iso : ClassicalGroup.IsPSL G 2 p)
  | janko (iso : Nonempty (G ≃* Janko1.Model))

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- Transport the model list by composing actual group isomorphisms. -/
theorem NonnormalCComponentModel.of_mulEquiv (h : NonnormalCComponentModel G)
    (e : H ≃* G) : NonnormalCComponentModel H := by
  cases h with
  | linear_even n hn iso => exact .linear_even n hn (iso.of_mulEquiv e)
  | suzuki m hm iso => exact .suzuki m hm (iso.map (e.trans ·))
  | linear_prime p hp ho iso => exact .linear_prime p hp ho (iso.of_mulEquiv e)
  | janko iso => exact .janko (iso.map (e.trans ·))

variable [Finite G]

/-- The quotient-lifting deduction for 1.2.1(3), using the normalizer index for orbit length. -/
theorem proposition_1_2_1_three_index_of_A_3_8 {𝒦 : GroupClass.{u}}
    (hA38 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ B : Subgroup X, B.IsCComponent →
      B.Normal ∨ (normalizer (B : Set X)).index = 2 ∧ NonnormalCComponentModel B)
    (hQ : IsSQTK 𝒦 (G ⧸ pCore 2 G))
    {B : Subgroup G} (hB : B.IsCComponent) :
    B.Normal ∨ (normalizer (B : Set G)).index = 2 ∧
      NonnormalCComponentModel (B ⧸ pCore 2 B) := by
  let := pCore_isNilpotent (p := 2) (G := G)
  rcases hA38 _ hQ (pCore_quotient_pCore_eq_bot 2) _ (hB.map_quotient _) with hn | ⟨hi, hm⟩
  · exact Or.inl (cComponent_normal_of_quotient_normal hB _ hn)
  · exact Or.inr ⟨(cComponent_normalizer_index_quotient hB _).symm.trans hi,
      hm.of_mulEquiv (cComponentTwoCoreQuotientEquiv hB)⟩

/-- Unique containment and relative normality in 1.2.4, from the universal earlier A.3 results. -/
theorem lemma_1_2_4_containment_normality_of_A_3_12_A_3_8 {𝒦 : GroupClass.{u}}
    (hA312 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ (T : Sylow 2 X) (B : Subgroup X),
      B ∈ ChapterA.Section03.localCComponents T →
      ∃! K : Subgroup X, K.IsCComponent ∧ B ≤ K)
    (hA38 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ K : Subgroup X, K.IsCComponent →
      K.Normal ∨ (normalizer (K : Set X)).index = 2 ∧ NonnormalCComponentModel K)
    (hQ : IsSQTK 𝒦 (G ⧸ pCore 2 G))
    (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ L G S) :
    ∃ K : Subgroup G, K.IsCComponent ∧ B ≤ K ∧
      (∀ D : Subgroup G, D.IsCComponent → B ≤ D → D = K) ∧
      ((S : Subgroup G) ≤ normalizer (B : Set G) → K.Normal) := by
  obtain ⟨K, ⟨hK, hBK⟩, hu⟩ := lemma_1_2_4_containment_of_A_3_12 hA312 hQ S hB
  refine ⟨K, hK, hBK, fun D hD hBD => hu D ⟨hD, hBD⟩, ?_⟩
  intro hSB
  apply cComponent_normal_of_unique_of_orbit_two hK hBK
    (fun D hD hBD => hu D ⟨hD, hBD⟩) S hSB
  exact (proposition_1_2_1_three_index_of_A_3_8 hA38 hQ hK).imp_right And.left

/-- Proposition 1.2.1(3), with the cardinality of the actual conjugacy family. -/
theorem proposition_1_2_1_three_of_A_3_8 {𝒦 : GroupClass.{u}}
    (hA38 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ B : Subgroup X, B.IsCComponent →
      B.Normal ∨ (normalizer (B : Set X)).index = 2 ∧ NonnormalCComponentModel B)
    (hQ : IsSQTK 𝒦 (G ⧸ pCore 2 G))
    {B : Subgroup G} (hB : B.IsCComponent) :
    B.Normal ∨ (Set.range fun g : G => B.map (MulAut.conj g).toMonoidHom).ncard = 2 ∧
      NonnormalCComponentModel (B ⧸ pCore 2 B) := by
  rw [ncard_conjugates_eq_index_normalizer]
  exact proposition_1_2_1_three_index_of_A_3_8 hA38 hQ hB

end CFSG.Quasithin.Chapter1.Section02
