module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Basic
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Source
public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms
public import Theory.GroupTheory.CyclicOuterCentralizer

/-!
# The proper pair residual in the binary linear case

Let L be the actual proper residual subgroup with its PSL₂(2ⁿ) marking,
and D the original two-point stabilizer. Once C_G(L) has order two, its
relative centralizer in N_G(L) is central. The proved cyclic outer group
makes N_G(L)/L abelian, so [D,D] lies in the actual odd subgroup D ∩ L.
Consequently D has even abelianization. Focal transfer gives O²(D) < D.

The final application supplies precisely this residual premise to the
existing normal-complement contradiction. The order-two centralizer and
normal complement remain the independent source conclusions of Lemmas 15.6
and 15.7; neither is included as a proved conclusion here.

Source: GLS IV, Chapter 2, Lemma 15.2(b), Lemma 15.6 and the paragraph
following Lemma 15.7 (refs/KGroup/GLS4/Chapter2.tex).
-/

noncomputable section
open Subgroup
open scoped IsMulCommutative commutatorElement

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
universe u

/-- The original pair-group commutator lies in L once C_G(L) has order two. -/
public theorem pair_derived_le_linear_of_centralizer_two
    {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    {n : ℕ} (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2) :
    (commutator (residualPairStabilizer M t)).map
      (residualPairStabilizer M t).subtype ≤ residualGenerated M z t := by
  let L := residualGenerated M z t
  let D := residualPairStabilizer M t
  let N := normalizer (L : Set G)
  let A := L.subgroupOf N
  let : A.Normal := inferInstance
  let eA : A ≃* MatrixGroups.PSL2BinaryMatrixGroup n :=
    (subgroupOfEquivOfLe L.le_normalizer).trans e
  let : IsCyclic (MulAut.Outer (MatrixGroups.PSL2BinaryMatrixGroup n)) :=
    Theory.PSL2.outer_isCyclic (BinaryGaloisField n)
  let : IsCyclic (MulAut.Outer A) :=
    isCyclic_of_surjective (MulAut.outerCongr eA).symm.toMonoidHom
      (MulAut.outerCongr eA).symm.surjective
  have hC : centralizer (A : Set N) = (centralizer (L : Set G)).subgroupOf N := by
    ext x
    constructor
    · intro hx l hl
      exact congrArg Subtype.val (hx ⟨l, L.le_normalizer hl⟩ hl)
    · intro hx l hl
      exact Subtype.ext (hx l hl)
  have hcard : Nat.card (centralizer (A : Set N)) = 2 := by
    rw [hC, Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer L)).toEquiv]
    exact hJ
  let : IsMulCommutative (N ⧸ A) := quotient_commutative_of_centralizer_two A hcard
  have hDN : D ≤ N := residualPairStabilizer_le_normalizer_residualGenerated
    h r ha hz hzM ht htM hL heven
  let f : D →* N ⧸ A := (QuotientGroup.mk' A).comp (inclusion hDN)
  have hcomm : commutator D ≤ f.ker := by
    change ⁅(⊤ : Subgroup D), ⊤⁆ ≤ f.ker
    apply commutator_le.mpr
    intro x _ y _
    change f ⁅x, y⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  rintro x ⟨a, ha, rfl⟩
  exact (QuotientGroup.eq_one_iff (inclusion hDN a)).mp (hcomm ha)

end BenderSuzuki.ZD

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
universe u

private theorem residual_proper_of_even_abelianization
    {G : Type u} [Group G] [Finite G]
    (heven : Even (Nat.card (G ⧸ commutator G))) :
    External.hallPResidual 2 G ≠ ⊤ := by
  let S : Sylow 2 G := Classical.choice inferInstance
  have hf : ControlsFusionIn (⊤ : Subgroup G) (S : Subgroup G) := by
    apply ControlsFusionIn.of_conjugators
    intro x y _ _ hxy
    obtain ⟨g, hg⟩ := isConj_iff.mp hxy
    exact ⟨⟨g, mem_top g⟩, hg⟩
  have hcard : Nat.card ((⊤ : Subgroup G) ⧸ derivedSubgroup (⊤ : Subgroup G)) =
      Nat.card (G ⧸ commutator G) := by
    simp only [derivedSubgroup, derivedSeries_one]
    let e : (⊤ : Subgroup G) ≃* G := Subgroup.topEquiv
    apply Nat.card_congr (QuotientGroup.congr _ _ e ?_).toEquiv
    have hr : (e : (⊤ : Subgroup G) →* G).range = ⊤ :=
      MonoidHom.range_eq_top_of_surjective _ e.surjective
    rw [map_commutator_eq, hr]
    rfl
  exact (hallPResidual_lt_top_of_dvd_abelianization_of_controlsFusionIn
    (⊤ : Subgroup G) S le_top hf (hcard.symm ▸ heven.two_dvd)).ne

/-- The genuine odd pair intersection and cyclic outer action give O²(D) < D. -/
public theorem proper_linear_pairResidual_of_centralizer_two
    {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    {n : ℕ} (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2) :
    External.hallPResidual 2 (residualPairStabilizer M t) ≠ ⊤ := by
  let D := residualPairStabilizer M t
  let K := D ⊓ residualGenerated M z t
  have hcomm : (commutator D).map D.subtype ≤ K :=
    le_inf (map_subtype_le _) (pair_derived_le_linear_of_centralizer_two
      h r ha hz hzM ht htM hL heven e hJ)
  have hoddK : Odd (Nat.card K) :=
    pair_inf_proper_residualGenerated_odd h.disconnected r hz hzM ht htM hL
  have hdiv : Nat.card (commutator D) ∣ Nat.card K := by
    have hle := card_dvd_of_le hcomm
    rwa [card_map_of_injective D.subtype_injective] at hle
  have hodd : Odd (Nat.card (commutator D)) := Odd.of_dvd_nat hoddK hdiv
  apply residual_proper_of_even_abelianization
  have hcard := card_eq_card_quotient_mul_card_subgroup (commutator D)
  change Even (Nat.card D) at heven
  rw [hcard, Nat.even_mul] at heven
  exact heven.resolve_right (Nat.not_even_iff_odd.mpr hodd)

end BenderSuzuki.ZD

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
universe u

/-- Apply the residual consequence to the original normal-complement endpoint. -/
public theorem linearExclusion_of_centralizer_two_and_normalComplement
    {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    {n : ℕ} (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (N : Subgroup M) (hN : N.Normal)
    (hsplit : ((residualPairStabilizer M t).subgroupOf M).IsComplement' N) : False :=
  linearExclusion_of_pair_normalComplement r h.disconnected N hN hsplit
    (proper_linear_pairResidual_of_centralizer_two h r ha hz hzM ht htM hL heven e hJ)

end BenderSuzuki.ZD
