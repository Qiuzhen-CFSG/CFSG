module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.CentralCover.Quotient
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.CentralCover.PairGeneration
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.CentralCover.Unitary

/-!
# The model alternatives for the proper residual subgroup

Strong embedding recognizes the literal odd-core quotient of `L`. The residual
commutators generate the whole quotient inside `borelPairGenerated`, whereas
the checked unitary calculation makes this subgroup proper in PSU₃: after
normalizing the two Borels and the outside involution, all its generators
preserve the nonisotropic middle line. This excludes the unitary alternative.
The odd central kernel then vanishes, giving actual PSL₂ or Suzuki models of
`L`, with their source parameter restrictions.

The final theorem discharges the unitary premise of the conditional reduction.
The distinguished-closure containment and normalization by the two-point
stabilizer remain explicit for the parent Lemma 12.2 assembly to supply.
Source: GLS4, Chapter 2, Corollary 7.13 and Lemma 12.2(a), and Chapter 4,
Lemmas 2.8(a) and 3.2(h).
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup _root_.BenderSuzuki.MatrixGroups
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The central cover and the actual residual generators reduce the source
model alternative to one independent calculation in the unitary matrix model. -/
public theorem proper_residualGenerated_models_of_unitary_pair_generation
    (hunitary : ∀ (n : ℕ), 2 ≤ n → ∀ (E : Type) [Field E] [Finite E]
      (J : HermitianForm 3 E) [Finite (ProjectiveSpecialUnitaryMatrixGroup J)],
      J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] →
      Nat.card E = (2 ^ n) ^ 2 →
      Nat.card {x : E // J.conj x = x} = 2 ^ n →
      ∀ (B : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)), IsBorelSubgroup B →
      ∀ (z t : ProjectiveSpecialUnitaryMatrixGroup J),
        PFAppendixIII.IsInvolution z → z ∈ B → PFAppendixIII.IsInvolution t → t ∉ B →
        borelPairGenerated B z t ≠ ⊤)
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hDN : residualPairStabilizer M t ≤ normalizer (residualGenerated M z t : Set G)) :
    ∃ n : ℕ, 2 ≤ n ∧
      (Nonempty (residualGenerated M z t ≃* PSL2BinaryMatrixGroup n) ∨
        ∃ m : ℕ, 1 ≤ m ∧ n = 2 * m + 1 ∧
          Nonempty (residualGenerated M z t ≃* SuzukiMatrixGroup m)) := by
  have hrec := proper_residualGenerated_quotient_recognition h r hz hzM ht htM hL hAL
  obtain ⟨n, hn, hmodel⟩ := hrec.1.exists_exponent
  refine ⟨n, hn, ?_⟩
  apply proper_residualGenerated_lift_quotient_models h r ha hz hzM ht htM hL hAL hn
  rcases hmodel with hpsl | hsuzuki | hpsu
  · exact Or.inl hpsl
  · exact Or.inr hsuzuki
  · exfalso
    obtain ⟨E, hfield, hfinite, J, hJ, hcard, hfixed, ⟨e⟩⟩ := hpsu
    let : Field E := hfield
    let : Finite E := hfinite
    let L := residualGenerated M z t
    let N := twoPrimeCore L
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_equiv (L ⧸ N) e.toEquiv
    let q := QuotientGroup.mk' N
    let f := e.toMonoidHom.comp q
    let B := M.comap L.subtype
    let BQ := B.map f
    let zL : L := ⟨z, (le_sup_left.trans le_sup_left : zpowers z ≤ L) (mem_zpowers z)⟩
    let tL : L := ⟨t, (le_sup_right.trans le_sup_left : zpowers t ≤ L) (mem_zpowers t)⟩
    have hBorel : IsBorelSubgroup BQ := by
      simpa only [map_map] using hrec.2.map_mulEquiv e
    have hodd : Odd (Nat.card N) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
    have hzI : PFAppendixIII.IsInvolution (f zL) := IsInvolution.map_of_injective
      (IsInvolution.quotient_mk_of_odd_kernel N hodd
        (IsInvolution.subtype (h.disconnected.involutions z hz) zL.property))
      e.toMonoidHom e.injective
    have htI : PFAppendixIII.IsInvolution (f tL) := IsInvolution.map_of_injective
      (IsInvolution.quotient_mk_of_odd_kernel N hodd
        (IsInvolution.subtype (h.disconnected.involutions t ht) tL.property))
      e.toMonoidHom e.injective
    have hzB : f zL ∈ BQ := mem_map_of_mem f hzM
    have htB : f tL ∉ BQ := by
      intro hx
      obtain ⟨x, hxB, he⟩ := hx
      have hqx : q x = q tL := e.injective he
      have hNB : N ≤ B := by
        intro y hy
        exact oddCore_le_of_distinguishedClosure_le h r L hAL (mem_map_of_mem L.subtype hy)
      apply htM
      exact (quotient_mk_mem_map_iff_of_le N B hNB tL).mp ⟨x, hxB, hqx⟩
    exact hunitary n hn E J hJ hcard hfixed BQ hBorel (f zL) (f tL) hzI hzB htI htB
      (borelPairGenerated_eq_top_of_residualGenerated M z t hDN e)

/-- Lemma 12.2(a), conditional only on the two orbit-control conclusions of
Lemma 3.10. The actual residual generators exclude the unitary quotient, and
the odd central-cover argument identifies `L` itself with the remaining models.
The source evenness hypothesis is retained although this step does not need it. -/
public theorem proper_residualGenerated_models_of_orbit_control
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (_heven : Even (Nat.card (residualPairStabilizer M t)))
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hDN : residualPairStabilizer M t ≤ normalizer (residualGenerated M z t : Set G)) :
    ∃ n : ℕ, 2 ≤ n ∧
      (Nonempty (residualGenerated M z t ≃* PSL2BinaryMatrixGroup n) ∨
        ∃ m : ℕ, 1 ≤ m ∧ n = 2 * m + 1 ∧
          Nonempty (residualGenerated M z t ≃* SuzukiMatrixGroup m)) :=
  proper_residualGenerated_models_of_unitary_pair_generation
    unitary_borelPairGenerated_ne_top h r ha hz hzM ht htM hL hAL hDN

end BenderSuzuki.ZD
