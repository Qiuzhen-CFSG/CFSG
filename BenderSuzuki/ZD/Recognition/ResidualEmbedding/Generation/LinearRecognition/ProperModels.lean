module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.Foundations
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.OrbitControl
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.CentralCover
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.LocalStructure

/-!
# The proper residual subgroup: GLS Lemma 12.2

For `L = ⟨z,t,[O₂′(D),t]⟩` proper in a minimal counterexample, the
distinguished orbit calculation puts `A = ⟨Z ∩ M⟩` in `L` and proves that
`D` normalizes `L`. Rank two and local strong embedding recognize the
odd-core quotient of `L`. The actual generators exclude the unitary quotient,
and the central-cover argument identifies `L` itself with a PSL₂ or Suzuki
matrix group.

The Borel calculations then give every local clause of Lemma 12.2 with the
same parameter `q = 2^n`: relative normality and elementary abelian structure
of `A`, the involution-product equality, both normalizer products, the mixed
dihedral description, and the cyclic group `K = D ∩ L` equal to the inverted
set in `O₂′(D)`. All containment and model premises of those calculations are
discharged here. The Suzuki parameter is `n = 2*m+1`, with `m ≥ 1`.

Source: `refs/KGroup/GLS4/Chapter2.tex`, Lemma 12.2(a–f), using Lemma 3.10,
Corollary 7.13, and Chapter 4, Lemmas 2.8(a) and 3.2.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Lemma 12.2(a): the proper residual subgroup itself has an actual PSL₂ or
Suzuki matrix model, with no extra containment or quotient-model premises. -/
public theorem proper_residualGenerated_models
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t))) :
    ∃ n : ℕ, 2 ≤ n ∧
      (Nonempty (residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n) ∨
        ∃ m : ℕ, 1 ≤ m ∧ n = 2 * m + 1 ∧
          Nonempty (residualGenerated M z t ≃* MatrixGroups.SuzukiMatrixGroup m)) :=
  proper_residualGenerated_models_of_orbit_control h r ha hz hzM ht htM hL heven
    (proper_residualGenerated_contains_distinguishedClosure h r ha hz hzM ht htM hL heven)
    (residualPairStabilizer_le_normalizer_residualGenerated h r ha hz hzM ht htM hL heven)

/-- All clauses of GLS4, Chapter 2, Lemma 12.2(a–f), under the original
proper-residual hypotheses. The common witness `n` simultaneously gives the
actual model, the order of the elementary abelian distinguished closure, and
the order of the cyclic residual commutator. The conclusion also retains
`A ≤ L`, normalization by `D`, and the uniqueness of the rotation involution.

Normality of `A` is inside `M`. The normalizer equalities are literal set
products, and `T` is the ambient image of the local Sylow two-core. The
inverted set in clause (f) uses the odd core of `D`. -/
public theorem proper_residualGenerated_structure
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t))) :
    let L := residualGenerated M z t
    let D := residualPairStabilizer M t
    let K := residualCommutator M t
    let A := closure (Z ∩ (M : Set G))
    let B := M ⊓ L
    let T := (pCore 2 B).map B.subtype
    ∃ n : ℕ, 2 ≤ n ∧
      (Nonempty (L ≃* MatrixGroups.PSL2BinaryMatrixGroup n) ∨
        ∃ m : ℕ, 1 ≤ m ∧ n = 2 * m + 1 ∧
          Nonempty (L ≃* MatrixGroups.SuzukiMatrixGroup m)) ∧
      A ≤ L ∧ D ≤ normalizer (L : Set G) ∧
      closure (Z ∩ (B : Set G)) = A ∧
      (involutionCore B).map B.subtype = A ∧
      (A.subgroupOf M).Normal ∧
      IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ n ∧
      Z ∩ (M : Set G) = (A : Set G) \ {1} ∧
      {v : G | PFAppendixIII.IsInvolution v ∧ ∃ x ∈ Z, ∃ y ∈ Z, v = x * y} = Z ∧
      (normalizer (L : Set G) : Set G) = (L : Set G) * (D : Set G) ∧
      centralizer (L : Set G) ≤ D ∧
      ((M ⊓ normalizer (L : Set G) : Subgroup G) : Set G) = (T : Set G) * (D : Set G) ∧
      (∃ S : Sylow 2 B, (S : Subgroup B) = pCore 2 B) ∧
      D ≤ normalizer (T : Set G) ∧
      K = D ⊓ L ∧ IsCyclic K ∧ Nat.card K = 2 ^ n - 1 ∧
      (K : Set G) = {x | x ∈ (pPrimeCore 2 D).map D.subtype ∧
        rightConjugateElem x t = x⁻¹} ∧
      (∀ u : G, PFAppendixIII.IsInvolution u → u ∉ Z →
        let H := closure ({u, z} : Set G)
        let R := zpowers (u * z)
        let w := (u * z) ^ (orderOf (u * z) / 2)
        ((∃ k : ℕ, Odd k ∧ Nat.card H = 4 * k) ∨ Nat.card H = 8) ∧
          w ∈ R ∧ PFAppendixIII.IsInvolution w ∧
          (∀ v ∈ R, PFAppendixIII.IsInvolution v → v = w) ∧
          (Nat.card H = 8 → closure ({w, z} : Set G) ≤ A ∧
            u ∈ M ∧ u ∉ centralizer (A : Set G))) := by
  have hAL := proper_residualGenerated_contains_distinguishedClosure
    h r ha hz hzM ht htM hL heven
  have hDN := residualPairStabilizer_le_normalizer_residualGenerated
    h r ha hz hzM ht htM hL heven
  obtain ⟨n, hn, hmodels⟩ :=
    proper_residualGenerated_models h r ha hz hzM ht htM hL heven
  exact ⟨n, hn, hmodels, hAL, hDN,
    proper_residualGenerated_local_structure_of_models h r hz hzM ht htM hL hAL hDN hn hmodels⟩

end BenderSuzuki.ZD
