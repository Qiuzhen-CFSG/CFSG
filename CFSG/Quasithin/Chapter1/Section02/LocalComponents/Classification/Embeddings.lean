module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Orbits

/-!
# The twenty-two alternatives in A.3.12

The alternatives retain the actual pair of subgroups. In the parabolic cases,
the subgroup is the embedded solvable residual of a parabolic of the containing
component. Here a finite characteristic-two Lie parabolic means an overgroup
of a Borel, expressed as the normalizer of a Sylow two-subgroup of the specified
Lie group. Maximal parabolic means maximal proper such overgroup.

All extensions have a normal kernel of the displayed type and the displayed
quotient; no splitting is imposed. The final two cases use the intrinsic odd
core of the containing group and the actual image of the smaller subgroup.

The quotient deduction lifts the specified component, retaining its exact
image, so the embedding alternatives apply to the images of the actual lifted
subgroups. The universal A.3.12 and A.3.8 inputs retain all A.3.4 hypotheses.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, A.3.12, pp.47–48,
and Lemma 1.2.4, p.505.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter1.Section02
open LocalModels
universe u

/-- The exceptional prime congruences in A.3.12(8),(22). -/
def A312ExceptionalPrime (p : ℕ) : Prop :=
  p.Prime ∧ Odd p ∧ p ^ 2 % 5 = 1 ∧ (p % 8 = 3 ∨ p % 8 = 5)

/-- Finite Lie parabolic in characteristic two, using the Sylow-normalizer Borel. -/
def LieParabolicTwo {K : Type u} [Group K] (P : Subgroup K) : Prop :=
  ∃ T : Sylow 2 K, normalizer (T : Set K) ≤ P

/-- The actual embedded solvable residual, not the two-core or two-residual. -/
def IsParabolicResidual {G : Type u} [Group G] (B K : Subgroup G)
    (maximal : Bool) : Prop :=
  ∃ P : Subgroup K, LieParabolicTwo P ∧ (maximal = true → IsCoatom P) ∧
    (solvableResidual P).map (K.subtype.comp P.subtype) = B

/-- Exactly the twenty-two numbered alternatives, including all subalternatives. -/
inductive A312Embedding {G : Type u} [Group G] (B K : Subgroup G) : Prop
  | one (eq : B = K)
  | two (n : ℕ) (hn : 2 ≤ n)
      (small : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2 ^ n))
      (large : RankTwoTheoremC K) (residual : IsParabolicResidual B K true)
  | three (m : ℕ) (hm : 1 ≤ m)
      (small : Nonempty ((B ⧸ pCore 2 B) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))
      (large : IsReeF4At K m) (residual : IsParabolicResidual B K false)
  | four (small : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 3 2)
      (large : ClassicalGroup.IsPSL K 4 2 ∨ ClassicalGroup.IsPSL K 5 2)
      (residual : IsParabolicResidual B K false)
  | five (small : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2)
      (large : ClassicalGroup.IsPSL K 5 2) (residual : IsParabolicResidual B K false)
  | six (small : IsAlternating B 5 ∨ ClassicalGroup.IsPSL B 3 2)
      (large : IsAlternating K 7 ∨ IsAlternatingCover K 7)
  | seven (models :
      (IsAlternating B 6 ∧ IsAlternating K 7) ∨
      (IsAlternatingCover B 6 ∧ IsAlternatingCover K 7))
  | eight (models :
      (∃ p : ℕ, p.Prime ∧ Odd p ∧ 3 < p ∧
        ClassicalGroup.IsPSL B 2 p ∧ ClassicalGroup.IsPSL K 2 (p ^ 2)) ∨
      (∃ p : ℕ, A312ExceptionalPrime p ∧ IsAlternating B 5 ∧ ClassicalGroup.IsPSL K 2 p))
  | nine (models :
      (∃ (p : ℕ) (unitary : Bool), p.Prime ∧ Odd p ∧ 3 < p ∧ IsSL B 2 p ∧
        (IsPSLSign K unitary 3 p ∨ IsSLSign K unitary 3 p)) ∨
      (IsAlternating B 6 ∧ ClassicalGroup.IsPSU K 3 5) ∨
      (IsAlternatingCover B 6 ∧ IsSU K 3 5))
  | ten (p : ℕ) (hp : p.Prime) (ho : Odd p) (hlarge : 3 < p)
      (small : HasExtension B (ElementaryModel p 2) (fun X _ => IsSL X 2 p))
      (large : ClassicalGroup.IsPSL K 3 p ∨ IsSL K 3 p)
  | eleven (small : IsAlternating B 6) (large : Nonempty (K ≃* Sporadic.Mathieu.M11))
  | twelve (models :
      (HasExtension B (ElementaryModel 2 4)
          (fun X _ => IsAlternating X 5 ∨ IsAlternating X 6) ∧
        Nonempty (K ≃* Sporadic.Mathieu.M22)) ∨
      (HasExtension B (ElementaryModel 2 4)
          (fun X _ => IsAlternating X 5 ∨ IsAlternatingCover X 6) ∧ IsM22Cover K))
  | thirteen (large : Nonempty (K ≃* Sporadic.Mathieu.M23))
      (small : Nonempty (B ≃* Sporadic.Mathieu.M22) ∨ ClassicalGroup.IsPSL B 3 4 ∨
        HasExtension B (ElementaryModel 2 4)
          (fun X _ => IsAlternating X 7 ∨ ClassicalGroup.IsPSL X 3 2 ∨
            IsAlternating X 6 ∨ IsAlternating X 5) ∨
        HasExtension B (ElementaryModel 2 3) (fun X _ => ClassicalGroup.IsPSL X 3 2))
  | fourteen (large : Nonempty (K ≃* Sporadic.Mathieu.M24))
      (small : HasExtension B (ElementaryModel 2 4) (fun X _ => ClassicalGroup.IsPSL X 4 2) ∨
        HasExtension B (ElementaryModel 2 6)
          (fun X _ => ClassicalGroup.IsPSL X 3 2 ∨ IsAlternatingCover X 6) ∨
        HasExtension B (ExtraspecialModel 2 3) (fun X _ => ClassicalGroup.IsPSL X 3 2))
  | fifteen (small : IsAlternating B 5) (large : Nonempty (K ≃* Janko1.Model))
  | sixteen (small : HasExtension B (ExtraspecialModel 2 2) (fun X _ => IsAlternating X 5))
      (large : Nonempty (K ≃* Sporadic.LeechRelated.J2.Carrier))
  | seventeen (large : Nonempty (K ≃* Janko4.Model))
      (small : HasExtension B (ExtraspecialModel 2 6) IsM22Cover ∨
        HasExtension B (ElementaryModel 2 11) (fun X _ => Nonempty (X ≃* Sporadic.Mathieu.M24)) ∨
        IsAlternating (B ⧸ pCore 2 B) 5 ∨ IsAlternatingCover (B ⧸ pCore 2 B) 6 ∨
        ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2 ∨ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 3 2)
  | eighteen (large : Nonempty (K ≃* Sporadic.LeechRelated.HS.Carrier))
      (small : HasExtension B (CyclicFourCentralProduct 2) (fun X _ => IsAlternating X 5) ∨
        HasExtension B (fun X _ => Nonempty (X ≃* Multiplicative (Fin 3 → ZMod 4)))
          (fun X _ => ClassicalGroup.IsPSL X 3 2))
  | nineteen (large : Nonempty (K ≃* Held.He))
      (small : HasExtension B (ExtraspecialModel 2 3) (fun X _ => ClassicalGroup.IsPSL X 3 2) ∨
        HasExtension B (ElementaryModel 2 6) (fun X _ => IsAlternatingCover X 6))
  | twenty (large : Nonempty (K ≃* Rudvalis.Model))
      (small : IsAlternating (B ⧸ pCore 2 B) 5 ∨ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 3 2)
      (kernel : Nat.card (pCore 2 B) = 2 ^ 11)
  | twenty_one (p : ℕ) (hp : p.Prime) (ho : Odd p)
      (noncentral : ⁅pPrimeCore 2 K, (⊤ : Subgroup K)⁆ ≠ ⊥)
      (generation : B ⊔ (pPrimeCore 2 K).map K.subtype = K)
      (quotient : IsSL (K ⧸ pPrimeCore 2 K) 2 p)
  | twenty_two (p : ℕ) (hp : A312ExceptionalPrime p)
      (noncentral : ⁅pPrimeCore 2 K, (⊤ : Subgroup K)⁆ ≠ ⊥)
      (large : IsSL (K ⧸ pPrimeCore 2 K) 2 p)
      (image : IsSL ((B.subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 K))) 2 5)

/-- A.3.12's complete output: uniqueness is among all containing C-components. -/
def A312Conclusion {G : Type u} [Group G] (B : Subgroup G) : Prop :=
  ∃ K : Subgroup G, K.IsCComponent ∧ B ≤ K ∧
    (∀ D : Subgroup G, D.IsCComponent → B ≤ D → D = K) ∧ A312Embedding B K

/-- The model-valued lifting deduction in 1.2.4, including its normality consequence.
The group `G` here is the source's local group `H`; normality is relative to it. -/
theorem lemma_1_2_4_of_A_3_12_A_3_8 {G : Type u} [Group G] [Finite G]
    {𝒦 : GroupClass.{u}}
    (hA312 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ (T : Sylow 2 X) (B : Subgroup X),
      B ∈ ChapterA.Section03.localCComponents T → A312Conclusion B)
    (hA38 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ K : Subgroup X, K.IsCComponent →
      K.Normal ∨ (normalizer (K : Set X)).index = 2 ∧ NonnormalCComponentModel K)
    (hQ : IsSQTK 𝒦 (G ⧸ pCore 2 G))
    (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ L G S) :
    ∃ K : Subgroup G, K.IsCComponent ∧ B ≤ K ∧
      (∀ D : Subgroup G, D.IsCComponent → B ≤ D → D = K) ∧
      A312Embedding (B.map (QuotientGroup.mk' (pCore 2 G)))
        (K.map (QuotientGroup.mk' (pCore 2 G))) ∧
      ((S : Subgroup G) ≤ normalizer (B : Set G) → K.Normal) := by
  let := pCore_isNilpotent (p := 2) (G := G)
  let := mem_L_isPerfect hB
  let q := QuotientGroup.mk' (pCore 2 G)
  have hBq : B.map q ∈ ChapterA.Section03.localCComponents
      (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G))) := by
    simpa only [Sylow.coe_mapSurjective] using mem_L_map_twoCore_mem_localCComponents hB
  obtain ⟨Kbar, hKbar, hBKbar, hu, hemb⟩ := hA312 _ hQ (pCore_quotient_pCore_eq_bot 2)
    (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G))) _ hBq
  obtain ⟨K, hK, hBK, he⟩ := exists_cComponent_lift_containing_map (pCore 2 G) hKbar hBKbar
  have unique : ∀ D : Subgroup G, D.IsCComponent → B ≤ D → D = K := by
    intro D hD hBD
    apply hD.eq_of_map_quotient_eq hK (pCore 2 G)
    exact (hu _ (hD.map_quotient _) (map_mono hBD)).trans he.symm
  refine ⟨K, hK, hBK, unique, he.symm ▸ hemb, ?_⟩
  intro hSB
  apply cComponent_normal_of_unique_of_orbit_two hK hBK unique S hSB
  exact (proposition_1_2_1_three_index_of_A_3_8 hA38 hQ hK).imp_right And.left

end CFSG.Quasithin.Chapter1.Section02
