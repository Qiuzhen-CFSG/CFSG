module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.CentralCover.Unitary.Displacements
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.CentralCover.Unitary.Middle
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.CentralCover.Unitary.Normalization

/-!
# Properness of the unitary Borel-pair generated subgroup

Normalize the two Borel points using the actual isotropic-point action. The
outside involution then lies in the torus-Weyl coset. The inside involution
lies in the root Sylow subgroup, and its square forces first coordinate zero.
Both involutions therefore preserve the middle line. The literal displacements
of all pair-preserving automorphisms lie in the Borel intersection, which is
the torus after normalization and also preserves that line. An explicit root
moves the line, proving that the generated subgroup is proper.

This proves the precise matrix input to
`proper_residualGenerated_models_of_unitary_pair_generation`, with no
semilinear-coverage, normalization, exclusion, or invariant-line assumption.
Source: GLS4, Chapter 4, Lemma 3.2(d),(h), used in Chapter 2, Lemma 12.2(a).
-/

noncomputable section
namespace BenderSuzuki.ZD
open PFAppendixIII PFchapter1section1 Subgroup
open _root_.BenderSuzuki.MatrixGroups _root_.BenderSuzuki.MatrixGroups.HermitianForm
open OddPrimeSylow.NormalizedOuter.Coverage UnitaryPair

/-- In the actual binary unitary model the literal Borel-pair generated
subgroup is proper. Every extra geometric premise is discharged below. -/
public theorem unitary_borelPairGenerated_ne_top
    (n : ℕ) (hn : 2 ≤ n) (E : Type) [Field E] [Finite E]
    (J : HermitianForm 3 E) [Finite (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (B : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hB : IsBorelSubgroup B)
    (z t : ProjectiveSpecialUnitaryMatrixGroup J)
    (hz : PFAppendixIII.IsInvolution z) (hzB : z ∈ B)
    (ht : PFAppendixIII.IsInvolution t) (htB : t ∉ B) :
    borelPairGenerated B z t ≠ ⊤ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa [Nat.card_eq_fintype_card, pow_mul] using hcard)
  have hn0 : 0 < n := by omega
  obtain ⟨c, hcB, hcBt, k, hct⟩ :=
    exists_unitary_borel_pair_normalization J hJ hn0 hcard hfixed B hB t ht htB
  have hfirst := EvenSemilinear.coord_first_surjective J hcard hfixed 1
  let H := (middleSubgroup J).comap c.toMonoidHom
  have hH : H ≠ ⊤ := by
    intro he
    apply middleSubgroup_ne_top J hJ hfirst
    apply top_unique
    intro x _
    obtain ⟨y, rfl⟩ := c.surjective x
    have hy : y ∈ H := he ▸ mem_top y
    exact hy
  have htH : t ∈ H := by
    change c t ∈ middleSubgroup J
    rw [hct]
    exact (middleSubgroup J).mul_mem (torus_mem_middleSubgroup J hJ k)
      (weyl_mem_middleSubgroup J hJ)
  have hzN : c z ∈ normalizer (rootGroup J hJ : Set _) :=
    hcB ▸ mem_map_of_mem c.toMonoidHom hzB
  have hcz : PFAppendixIII.IsInvolution (c z) :=
    IsInvolution.map_of_injective hz c.toMonoidHom c.injective
  have hzU : c z ∈ rootGroup J hJ := by
    let P := EvenTwoRank.rootSylow J hJ hn0 hcard hfixed
    have hp : IsPGroup 2 (zpowers (c z)) := IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_of_pow_eq_one hcz.sq_eq_one)
    have hh : c z ∈ zpowers (c z) ⊓ normalizer (P : Set _) := ⟨mem_zpowers _, hzN⟩
    rw [hp.inf_normalizer_sylow P] at hh
    exact hh.2
  have hzH : z ∈ H := by
    obtain ⟨v, hv⟩ := hzU
    have hv2 : v ^ 2 = 1 := by
      apply root_injective J hJ
      rw [map_pow, hv, hcz.sq_eq_one, map_one]
    change c z ∈ middleSubgroup J
    rw [← hv]
    exact root_mem_middleSubgroup J hJ v
      ((EvenSemilinear.square_eq_one_iff_first_zero J v).mp hv2)
  have hBH : B ⊓ rightConjugate B t ≤ H := by
    intro x hx
    have hcx : c x ∈ rootTorus J hJ := by
      rw [EvenSemilinear.rootTorus_eq_normalizer_inf J hJ hfirst]
      exact ⟨hcB ▸ mem_map_of_mem c.toMonoidHom hx.1,
        hcBt ▸ mem_map_of_mem c.toMonoidHom hx.2⟩
    obtain ⟨a, ha⟩ := hcx
    change c x ∈ middleSubgroup J
    rw [← ha]
    exact torus_mem_middleSubgroup J hJ a
  have hN : normalizer (B : Set _) = B := by
    obtain ⟨_, P, rfl⟩ := hB
    exact P.normalizer_normalizer
  have hNt : normalizer (rightConjugate B t : Set _) = rightConjugate B t := by
    change normalizer ((B.map (MulAut.conj t⁻¹).toMonoidHom :
      Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) : Set (ProjectiveSpecialUnitaryMatrixGroup J)) = _
    rw [← map_equiv_normalizer_eq, hN]
    rfl
  have hle := borelPairGenerated_le_pair B H z t ht hN hNt hzH htH hBH
  intro he
  exact hH (top_unique (he ▸ hle))

end BenderSuzuki.ZD
