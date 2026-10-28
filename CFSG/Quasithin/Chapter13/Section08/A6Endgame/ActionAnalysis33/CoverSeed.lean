module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair.CoverHyperplanes
public import Theory.Representation.SixLetterRadicalDisplacement.SeedOrbits

/-!
# A cover transvection center avoids every conjugate seed

The actual common-center conjugation action identifies the image of the
order-two commutator with a pair vector in the five-dimensional augmentation
module. Transporting a supposed seed containment through the literal quotient
would put that vector in a permutation translate of the weight-four seed
plane. Weight separation excludes it. The constant line of the cover and
the original quotient kernel are both retained.

Source: Aschbacher--Smith, Lemma 13.8.33, printed p.966, second paragraph.
-/

public section
open Subgroup BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33
open CriticalGeometry.AsymmetricPair.CoverHyperplanes
open Representation.SixLetterRadicalDisplacement
variable {G : Type*} [Group G] {H V₃ V₁ : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

theorem cover_center_not_le_seed_conjugate
    (d : CoverCoordinates H V₃ V₁) (hseed : d.image V₃ = W)
    (B A : Subgroup G) (hBH : B ≤ H) (hB : Source.starImage H B ≠ ⊥)
    (hcard : Nat.card A = 2) (hdisj : V₁ ⊓ A = ⊥)
    (hc : ⁅Source.UH H V₃, B⁆ = A) (h : H) :
    ¬ A ≤ V₃.conjBy (h : G) := by
  intro hA
  obtain ⟨_, i, j, hij, hcenter, _⟩ :=
    d.starImage_order_two_of_commutator_line B A hBH hB hcard hdisj hc
  have hpair : pairCore i j ∈ d.image A := by
    rw [hcenter]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨u, hu, he⟩ := hpair
  change (u.toMul : G) ∈ A at hu
  obtain ⟨v, hv, hval⟩ := hA hu
  let vU : Source.UH H V₃ := ⟨v, le_conjugateSpanBy V₃ H hv⟩
  have hvW : d.coordinates (Additive.ofMul vU) ∈ W := by
    rw [← hseed]
    exact d.mem_image V₃ vU hv
  have hmove : act (d.groupEquiv (QuotientGroup.mk' (pCore 2 H) h))
      (d.coordinates (Additive.ofMul vU)) = pairCore i j := by
    rw [show act (d.groupEquiv (QuotientGroup.mk' (pCore 2 H) h))
        (d.coordinates (Additive.ofMul vU)) =
        d.coordinates (Additive.ofMul
          (⟨(h : G) * v * (h : G)⁻¹,
            (mem_normalizer_iff.mp (d.normalizes h.property) v).mp vU.property⟩ : Source.UH H V₃))
      from d.intertwines h vU]
    convert he using 1
    congr 1
    exact Subtype.ext hval
  exact pair_not_mem_seed_orbit
    (d.groupEquiv (QuotientGroup.mk' (pCore 2 H) h)) i j hij ⟨_, hvW, hmove⟩

end CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33
