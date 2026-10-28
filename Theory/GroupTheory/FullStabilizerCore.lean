module

public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Full stabilizer actions exclude a proper local core

If Y induces every automorphism of A fixing z and contains C_H(A), where
H normalizes A and centralizes z, then H=Y provided Y≤H. Match an element
of H with one of Y on A; their quotient lies in the relative centralizer.

Consequently a proper subgroup A of a normal two-subgroup P of Y cannot
be O₂(C_G(z)) when that centralizer has characteristic two. If it were,
characteristic two would supply C_H(A)≤A and force H=Y, putting all of P
in O₂(H). No assertion that A is normal in G is required.

This is the elementary core step in Aschbacher–Smith, *The Classification
of Quasithin Groups*, combined manuscript (1 March 2004), Theorem 12.7.7,
printed pp.841–842. The argument only uses the relative centralizer bound;
it avoids the stronger intermediate assertion C_G(A)=A in that passage.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- Full action on A, together with its relative centralizer, determines H. -/
theorem le_of_full_stabilizer (A Y H : Subgroup G)
    (z : G) (hz : z ∈ A) (hYH : Y ≤ H)
    (hHN : H ≤ normalizer (A : Set G))
    (hHz : H ≤ centralizer ({z} : Set G))
    (hC : H ⊓ centralizer (A : Set G) ≤ Y)
    (hlift : ∀ a : MulAut A, a ⟨z, hz⟩ = ⟨z, hz⟩ →
      ∃ y : Y, A.normalizerMonoidHom ⟨y, hHN (hYH y.property)⟩ = a) :
    H ≤ Y := by
  intro g hg
  let n : normalizer (A : Set G) := ⟨g, hHN hg⟩
  have hfix : A.normalizerMonoidHom n ⟨z, hz⟩ = ⟨z, hz⟩ := by
    apply Subtype.ext
    change g * z * g⁻¹ = z
    rw [mem_centralizer_singleton_iff.mp (hHz hg), mul_assoc,
      mul_inv_cancel, mul_one]
  obtain ⟨y, hy⟩ := hlift (A.normalizerMonoidHom n) hfix
  let m : normalizer (A : Set G) := ⟨y, hHN (hYH y.property)⟩
  have hk : n * m⁻¹ ∈ A.normalizerMonoidHom.ker := by
    change A.normalizerMonoidHom (n * m⁻¹) = 1
    rw [map_mul, map_inv,
      show A.normalizerMonoidHom m = A.normalizerMonoidHom n from hy]
    exact mul_inv_cancel _
  rw [normalizerMonoidHom_ker] at hk
  have hc : g * (y : G)⁻¹ ∈ centralizer (A : Set G) := hk
  have hd : g * (y : G)⁻¹ ∈ Y :=
    hC ⟨H.mul_mem hg (H.inv_mem (hYH y.property)), hc⟩
  simpa only [inv_mul_cancel_right] using Y.mul_mem hd y.property

/-- A proper candidate A cannot be the core if Y already has the full
z-stabilizer action on A. All normality is relative to H=C_G(z). -/
theorem core_ne_of_full_stabilizer (P Y A : Subgroup G) (z : G)
    (hz : z ∈ A) (hP : IsPGroup 2 P) (hPY : P ≤ Y)
    (hYP : Y ≤ normalizer (P : Set G))
    (hYC : Y ≤ centralizer ({z} : Set G)) (hAP : A ≤ P) (hnot : ¬ P ≤ A)
    (hYA : Y ≤ normalizer (A : Set G))
    (hC : centralizer ({z} : Set G) ⊓
      centralizer ((centralizer ({z} : Set G)).pCoreIn 2 : Set G) ≤
        (centralizer ({z} : Set G)).pCoreIn 2)
    (hlift : ∀ a : MulAut A, a ⟨z, hz⟩ = ⟨z, hz⟩ →
      ∃ y : Y, A.normalizerMonoidHom ⟨y, hYA y.property⟩ = a) :
    (centralizer ({z} : Set G)).pCoreIn 2 ≠ A := by
  intro he
  have hnormal : centralizer ({z} : Set G) ≤ normalizer (A : Set G) := by
    rw [← he]
    exact (centralizer ({z} : Set G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hCA : centralizer ({z} : Set G) ⊓ centralizer (A : Set G) ≤ A := by
    simpa only [he] using hC
  have hCY : centralizer ({z} : Set G) ≤ Y :=
    le_of_full_stabilizer A Y _ z hz hYC hnormal le_rfl
      (hCA.trans (hAP.trans hPY)) (by intro a ha; exact hlift a ha)
  have hle : P ≤ (centralizer ({z} : Set G)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes hP (hPY.trans hYC) (hCY.trans hYP)
  exact hnot (he ▸ hle)

end Subgroup
