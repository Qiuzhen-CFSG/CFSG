module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalFixedPair
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.MarkedComponent
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.SourceCubic

/-!
# Applying the original fixed pair to the orthogonal overcomponent argument

The source fixed-pair theorem supplies the original block memberships,
Sylow centralizers and fixed lines. The orthogonal coordinates therefore
only need to identify these prescribed vectors in the literal moved module.
Equivariance then gives a strict component in the original second-vector
centralizer via the marked component theorem. The second vector’s original
Sylow-fixed line supplies the cubic that excludes an alternating-seven quotient.

Source: Aschbacher–Smith 10.2.1, printed p.743. The remaining coordinate
identities are supplied by the separate original-axis alignment argument.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The intrinsic original vector pair discharges every group-geometric
marking in the strict-component consumer. -/
theorem source_a5_original_fixed_pair_strict_component
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    {t : G} (ht : t ∈ (T : Subgroup G)) (p : SourceA5OriginalFixedPair D t)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hHN : H ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G))
    (hred : IsPReduced 2 ((conjugateSpanBy
      (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H)) :
    let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H
    letI := hred.normal
    letI := hred.elementary
    ∀ (S : Subrepresentation (centralizerQuotient (W.subgroupOf H)))
      (c : S.toSubmodule ≃ₗ[ZMod 2] BinaryFourPlus.V)
      (ew : (H ⧸ centralizer (W.subgroupOf H : Set H)) ≃* BinaryFourPlus.Wreath),
      (∀ x v, c (S.toRepresentation x v) =
        (BinaryFourPlus.wreathToIsometry (ew x)).val (c v)) →
      ∀ (u₁ u₂ : S.toSubmodule) (a b : BinaryFourPlus.Plane),
      a ≠ 0 → b ≠ 0 → c u₁ = (a,0) → c u₂ = (0,b) →
      ((u₁.val.toMul : H) : G) = p.first →
      ((u₂.val.toMul : H) : G) = p.second →
      ∃ I : Subgroup G, L < I ∧ I ≤ centralizer ({p.second} : Set G) ∧
        (I.subgroupOf (centralizer ({p.second} : Set G))).IsCComponent ∧
        centralizer ({p.second} : Set G) ≤ normalizer (I : Set G) := by
  let := hred.normal
  let := hred.elementary
  dsimp only
  intro S c ew he u₁ u₂ a b ha hb hc₁ hc₂ hv₁ hv₂
  have h := source_a5_fixed_center_strict_component_of_coordinates D e hn hout
    hH hHN hred S c ew he u₁ u₂ a b ha hb hc₁ hc₂ t
  rw [hv₁,hv₂] at h
  exact h p.first_layer p.first_fixed ht p.second_layer p.second_sylow p.second_ne
    p.second_opposite p.second_centralizer

/-- The actual original pair yields a strict containing component whose
two-core quotient cannot be alternating seven. -/
theorem source_a5_original_fixed_pair_strict_component_not_seven
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    {t : G} (ht : t ∈ (T : Subgroup G)) (p : SourceA5OriginalFixedPair D t)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hHN : H ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G))
    (hred : IsPReduced 2 ((conjugateSpanBy
      (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H)) :
    let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H
    letI := hred.normal
    letI := hred.elementary
    ∀ (S : Subrepresentation (centralizerQuotient (W.subgroupOf H)))
      (c : S.toSubmodule ≃ₗ[ZMod 2] BinaryFourPlus.V)
      (ew : (H ⧸ centralizer (W.subgroupOf H : Set H)) ≃* BinaryFourPlus.Wreath),
      (∀ x v, c (S.toRepresentation x v) =
        (BinaryFourPlus.wreathToIsometry (ew x)).val (c v)) →
      ∀ (u₁ u₂ : S.toSubmodule) (a b : BinaryFourPlus.Plane),
      a ≠ 0 → b ≠ 0 → c u₁ = (a,0) → c u₂ = (0,b) →
      ((u₁.val.toMul : H) : G) = p.first →
      ((u₂.val.toMul : H) : G) = p.second →
      ∃ I : Subgroup G, L < I ∧ I ≤ centralizer ({p.second} : Set G) ∧
        (I.subgroupOf (centralizer ({p.second} : Set G))).IsCComponent ∧
        centralizer ({p.second} : Set G) ≤ normalizer (I : Set G) ∧
        ¬ Nonempty ((I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7)) := by
  let := hred.normal
  let := hred.elementary
  dsimp only
  intro S c ew he u₁ u₂ a b ha hb hc₁ hc₂ hv₁ hv₂
  obtain ⟨I,hLI,hIX,hI,hNI⟩ := source_a5_original_fixed_pair_strict_component D e hn hout
    ht p hH hHN hred S c ew he u₁ u₂ a b ha hb hc₁ hc₂ hv₁ hv₂
  exact ⟨I,hLI,hIX,hI,hNI,
    FixedCenterOvercomponent.source_conjugate_layer_component_not_seven D e hn hout
      t p.second ht p.second_layer p.second_fixed p.second_ne p.second_opposite
      I hLI.le hIX hI hNI⟩

end CFSG.Quasithin.Chapter10
