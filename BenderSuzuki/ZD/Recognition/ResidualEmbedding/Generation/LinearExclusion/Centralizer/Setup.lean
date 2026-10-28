module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Basic
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Source

/-!
# The source setup for the proper linear centralizer argument

For the actual proper residual subgroup `L ≃ PSL₂(2^n)`, the earlier source
results identify the distinguished subgroup `A`, the cyclic pair intersection
`K`, and the normalizers, with this same exponent `n`. The uniform counting
alternatives and the completed centralizer collapse give degree `2^(3*n)+1`.
Every involution of the pair stabilizer centralizes `L`.

The context contains only the original hypotheses of the linear branch.
In particular no two-core, TI, centralizer-order or complement conclusion
is assumed here. Normality of `A` is relative to `M`.

Source: GLS IV, Chapter 2, Lemmas 12.2, 12.9–12.11, Proposition 13.1,
and Lemma 15.2(b,f,g).
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1
open scoped Pointwise
universe u

/-- The original proper linear branch, with its actual marked model. -/
public structure Context {G : Type u} [Group G] [Finite G]
    (Z : Set G) (M : Subgroup G) (z t : G) (n : ℕ) where
  minimal : MinimalCounterexample Z M
  reduction : SimpleReduction Z M
  action : ResidualAction Z M
  z_mem : z ∈ Z
  z_mem_M : z ∈ M
  t_mem : t ∈ Z
  t_not_mem_M : t ∉ M
  proper : residualGenerated M z t ≠ ⊤
  even_pair : Even (Nat.card (residualPairStabilizer M t))
  parameter : 2 ≤ n
  model : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n

variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
include d

public theorem Context.distinguished_le :
    closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t :=
  proper_residualGenerated_contains_distinguishedClosure d.minimal d.reduction d.action
    d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper d.even_pair

public theorem Context.pair_normalizes :
    residualPairStabilizer M t ≤ normalizer (residualGenerated M z t : Set G) :=
  residualPairStabilizer_le_normalizer_residualGenerated d.minimal d.reduction d.action
    d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper d.even_pair

public theorem Context.distinguished_elementary_card :
    IsElementaryAbelian 2 (closure (Z ∩ (M : Set G))) ∧
      Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n :=
  psl2_distinguishedClosure_elementary_card d.minimal.disconnected d.reduction
    d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper ⟨d.model⟩ d.parameter
    d.distinguished_le

/-- Both literal normalizer products and the cyclic intersection `K` use
exactly the exponent of the supplied PSL₂ model. -/
public theorem Context.normalizer_pair_structure :
    let L := residualGenerated M z t
    let D := residualPairStabilizer M t
    let K := residualCommutator M t
    let B := M ⊓ L
    let P := (pCore 2 B).map B.subtype
    (normalizer (L : Set G) : Set G) = (L : Set G) * (D : Set G) ∧
      ((M ⊓ normalizer (L : Set G) : Subgroup G) : Set G) =
        (P : Set G) * (D : Set G) ∧
      K = D ⊓ L ∧ IsCyclic K ∧ Nat.card K = 2 ^ n - 1 := by
  obtain ⟨_, _, _, _, _, _, _, hN, _, hMN, _, _, hK, hcyc, hcard, _⟩ :=
    proper_residualGenerated_local_structure_of_models d.minimal d.reduction
      d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper d.distinguished_le
      d.pair_normalizes d.parameter (Or.inl ⟨d.model⟩)
  exact ⟨hN, hMN, hK, hcyc, hcard⟩

public theorem Context.counting : ResidualCentralizerCountingData Z M z t :=
  proper_residualGenerated_centralizer_counting_of_local d.minimal d.reduction d.action
    d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper d.even_pair
    (proper_residualGenerated_centralizer_local_data d.minimal d.reduction d.action
      d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper d.even_pair)

/-- The source 12.9 involutions are those of the actual two-point group. -/
public theorem Context.pair_involution_centralizes {v : G}
    (hvD : v ∈ residualPairStabilizer M t) (hv : PFAppendixIII.IsInvolution v) :
    v ∈ centralizer (residualGenerated M z t : Set G) :=
  d.counting.centralizes v hvD hv

public theorem Context.centralizer_closure {v : G}
    (hvD : v ∈ residualPairStabilizer M t) (hv : PFAppendixIII.IsInvolution v) :
    centralizerClosure Z v = residualGenerated M z t :=
  proper_residualGenerated_centralizerClosure d.minimal d.reduction d.action
    d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper d.even_pair v hvD hv

/-- Lemma 15.2(f) and the associated fixed-coset formula, with no remaining
counting or centralizer-recognition assumption. -/
public theorem Context.degree_and_fixed :
    Nat.card (G ⧸ M) = (2 ^ n) ^ 3 + 1 ∧
      ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
        Nat.card {beta : G ⧸ M // v • beta = beta} = 2 ^ n + 1 := by
  obtain ⟨k, _, hk, hcases⟩ := d.counting.cases
  have hkn : k = n := Nat.pow_right_injective (by decide : 2 ≤ 2)
    (hk.symm.trans d.distinguished_elementary_card.2)
  subst k
  rcases hcases with ⟨_, hdegree, hfixed⟩ | ⟨m, hm, _, ⟨e⟩, _⟩ |
      ⟨_, hunitary, _⟩
  · exact ⟨hdegree, fun v hvD hv => (hfixed v hvD hv).2⟩
  · exact (MatrixGroups.not_nonempty_psl2_char_two_equiv_suzuki
      (BinaryGaloisField n) (by omega : 0 < m)
      ⟨d.model.symm.trans e⟩).elim
  · obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card'
      (G := residualPairStabilizer M t) 2 d.even_pair.two_dvd
    have hvi : PFAppendixIII.IsInvolution (v : G) :=
      BenderSuzuki.IsInvolution.map_of_injective
        (orderOf_eq_prime_iff.mp hv).symm
        (residualPairStabilizer M t).subtype Subtype.val_injective
    have hlt := (hunitary v v.property hvi).1
    rw [d.centralizer_closure v.property hvi] at hlt
    exact (lt_irrefl _ hlt).elim

/-- The centralizer has even order because it contains every involution of D. -/
public theorem Context.centralizer_even :
    Even (Nat.card (centralizer (residualGenerated M z t : Set G))) := by
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card'
    (G := residualPairStabilizer M t) 2 d.even_pair.two_dvd
  have hvi : PFAppendixIII.IsInvolution (v : G) :=
    BenderSuzuki.IsInvolution.map_of_injective (orderOf_eq_prime_iff.mp hv).symm
      (residualPairStabilizer M t).subtype Subtype.val_injective
  let vJ : centralizer (residualGenerated M z t : Set G) :=
    ⟨v, d.pair_involution_centralizes v.property hvi⟩
  have hi := BenderSuzuki.IsInvolution.subtype hvi vJ.property
  exact even_iff_two_dvd.mpr ((orderOf_eq_prime_iff.mpr hi.symm) ▸ orderOf_dvd_natCard vJ)

public theorem Context.twoResidual_point_eq_top : External.hallPResidual 2 M = ⊤ :=
  d.reduction.linear_twoResidual_eq_top d.minimal.disconnected

end BenderSuzuki.ZD.LinearExclusion
