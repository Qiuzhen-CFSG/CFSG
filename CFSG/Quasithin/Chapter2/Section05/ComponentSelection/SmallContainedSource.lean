module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallNormalizerSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallIntersectionSource

/-!
# The original small-component contained-normalizer source branch

The genuine ambient hypotheses construct the marked involution, which now
constructs the exact GL2(3) intersection. The normalizer replacement theorem
then supplies a proper subgroup with the original Sylow and selected pair,
both starred conditions, and the enlarged literal normalizer family. Its
components are original components centralizing and distinct from the one
removed. No marking, intersection, normality, radical or Schreier premise
remains; the component model and the source branch guard are explicit.

Source: Aschbacher--Smith 2.5.2(3) and 2.5.3(4), printed pp.551--553.
The earlier full model sieve and the remaining component branches belong to
the final assembly; this module closes both small-model removal cases.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {M H U HU : Subgroup G}

/-- The original ambient source hypotheses discharge the exact intersection
input in the contained-normalizer branch for PSL3(3) and M11. -/
theorem small_component_contained_source
    {C : GroupClass} (hG : IsSimpleQTKE C G)
    (T₀ : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hT₀M : (T₀ : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T₀ : Subgroup G) ≤ N → N = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    {n : ℕ} (B : Fin n → Subgroup G)
    (hp : ∀ i, IsPGroup 2 (B i)) (hBH : ∀ i, B i ≤ H)
    (hHnorm : H = ⨅ i, normalizer (B i : Set G))
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hbig : H ∈ gammaStar (Chapter1.He G) M →
      ∀ V ∈ localBases (Chapter1.He G) M, Nat.card V ≤ Nat.card U)
    (hsat : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
      HU ≤ normalizer (P : Set G) → P ≤ twoCore HU)
    (D : Subgroup H) (hD : IsComponent H D)
    (hm : Nonempty (D ≃* Matrix.PSL3Three.PSL) ∨ Nonempty (D ≃* Sporadic.Mathieu.M11))
    (hinside : (D ⊓ normalizer ((D ⊓ (twoCore HU).subgroupOf H : Subgroup H) : Set H)).map
      H.subtype ≤ M)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    (hSM : (S : Subgroup H).map H.subtype ≤ M)
    (hQS : (twoCore HU).subgroupOf H ≤ (S : Subgroup H)) :
    let R := D ⊓ (twoCore HU).subgroupOf H
    let X := (normalizer (R : Set H)).map H.subtype
    ∃ B' : Fin (n + 1) → Subgroup G,
      X < H ∧ X ∈ gammaZero (Chapter1.He G) M ∧
      (H ∈ gammaStar (Chapter1.He G) M → X ∈ gammaStar (Chapter1.He G) M) ∧
      (H ∈ gammaMax (Chapter1.He G) M → X ∈ gammaMax (Chapter1.He G) M) ∧
      HU ≤ X ∧ (S : Subgroup H).map H.subtype ≤ X ∧
      (∀ i, IsPGroup 2 (B' i)) ∧ (∀ i, B' i ≤ X) ∧
      X = ⨅ i, normalizer (B' i : Set G) ∧
      ∀ K : Subgroup X, IsComponent X K →
        IsComponentIn (K.map X.subtype) H ∧
        K.map X.subtype ≤ centralizer (D.map H.subtype : Set G) ∧
        K.map X.subtype ≠ D.map H.subtype := by
  obtain ⟨S', z, h, _hz⟩ := exists_marking_of_saturated_pair hG T₀ hM hT₀M hunique
    hH B hp hBH hHnorm hpair hsat
  obtain ⟨e⟩ := small_intersection_equiv_gl2_of_source_marking h D hD hm
  exact small_component_normalizer_source hG.quasithin hH B hp hBH hHnorm
    hpair hbig hsat D hD hm hinside S hUS hSM hQS e

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
