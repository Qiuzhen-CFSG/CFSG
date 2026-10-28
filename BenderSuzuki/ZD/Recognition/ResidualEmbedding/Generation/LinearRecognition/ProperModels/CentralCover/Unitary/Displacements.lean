module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.CentralCover.PairGeneration

/-!
# Automorphism displacements for a Borel pair

An involution swaps a subgroup with its right conjugate. An automorphism
preserving both therefore has displacement in their common normalizer.
For self-normalizing subgroups this is their intersection. This bounds the
literal automorphism generators used in GLS4, Chapter 4, Lemma 3.2(d),(h),
and Chapter 2, Lemma 12.2(a), without assuming that the automorphism is inner.
-/

open BenderSuzuki PFAppendixIII PFchapter1section1 Subgroup
namespace BenderSuzuki.ZD
variable {G : Type*} [Group G]

private theorem pair_displacement_mem (B : Subgroup G) (t : G)
    (ht : PFAppendixIII.IsInvolution t)
    (hN : normalizer (B : Set G) = B)
    (hNt : normalizer (rightConjugate B t : Set G) = rightConjugate B t)
    (a : MulAut G) (hB : B.map a.toMonoidHom = B)
    (hBt : (rightConjugate B t).map a.toMonoidHom = rightConjugate B t) :
    a t * t⁻¹ ∈ B ⊓ rightConjugate B t := by
  have ha : (a t)⁻¹ = a t := by rw [← map_inv, ht.inv_eq_self]
  have he : B.conjBy (a t) = B.conjBy t := by
    have hh := rightConjugate_map B a.toMonoidHom t
    rw [hB, hBt] at hh
    simpa only [rightConjugate, ht.inv_eq_self, MulEquiv.coe_toMonoidHom, ha] using hh.symm
  have hswap : (rightConjugate B t).conjBy (a t) = B := by
    change (B.conjBy t⁻¹).conjBy (a t) = B
    rw [ht.inv_eq_self, ← he]
    simpa only [ha] using B.conjBy_inv (a t)
  constructor
  · rw [← hN]
    apply mem_normalizer_iff_map_conj_eq.mpr
    change B.conjBy (a t * t⁻¹) = B
    rw [conjBy_mul]
    exact hswap
  · rw [← hNt]
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (rightConjugate B t).conjBy (a t * t⁻¹) = rightConjugate B t
    rw [conjBy_mul]
    change ((B.conjBy t⁻¹).conjBy t⁻¹).conjBy (a t) = B.conjBy t⁻¹
    have htt : (B.conjBy t).conjBy t = B := by
      simpa only [ht.inv_eq_self] using B.conjBy_inv t
    rw [ht.inv_eq_self, htt, he]

/-- The literal Borel-pair generators lie in any subgroup containing the two
involutions and the Borel intersection. -/
public theorem borelPairGenerated_le_pair (B H : Subgroup G) (z t : G)
    (ht : PFAppendixIII.IsInvolution t)
    (hN : normalizer (B : Set G) = B)
    (hNt : normalizer (rightConjugate B t : Set G) = rightConjugate B t)
    (hz : z ∈ H) (htH : t ∈ H) (hBH : B ⊓ rightConjugate B t ≤ H) :
    borelPairGenerated B z t ≤ H := by
  apply sup_le (sup_le (zpowers_le.mpr hz) (zpowers_le.mpr htH))
  rw [closure_le]
  rintro x ⟨a, ha, hat, rfl⟩
  exact hBH (pair_displacement_mem B t ht hN hNt a ha hat)

end BenderSuzuki.ZD
