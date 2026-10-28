module

public import Theory.GroupTheory.SubgroupConjugation

/-!
# Conjugate placement through commuting quotient images

If a homomorphism's kernel lies in H, conjugation by an actor commuting
with the image of K <= H keeps K inside H. Applying the inverse conjugation
to normalizers then shows that K normalizes the corresponding conjugate of
any H-invariant subgroup. The kernel is the literal kernel inside the local
source group; no ambient normality or split extension is assumed.

Source application: the two commuting factors in Aschbacher–Smith,
The Classification of Quasithin Groups, 13.8.29(3), printed p.964.
-/

public section
open Subgroup
namespace Subgroup
variable {G D : Type*} [Group G] [Group D]

/-- Commuting quotient images preserve placement, provided the literal kernel lies in H. -/
theorem conjBy_le_of_commute_image
    (P H K : Subgroup G) (hKP : K ≤ P) (hKH : K ≤ H)
    (f : P →* D) (hker : f.ker ≤ H.subgroupOf P)
    (g : P) (hc : ∀ k : K, Commute (f g) (f (inclusion hKP k))) :
    K.conjBy (g:G) ≤ H := by
  rintro _ ⟨k,hk,rfl⟩
  let kP : P := inclusion hKP ⟨k,hk⟩
  have he : f (g * kP * g⁻¹ * kP⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [(hc ⟨k,hk⟩).eq]
    simp only [mul_inv_cancel_right]
    exact mul_inv_cancel _
  have hh := hker he
  have hm := H.mul_mem hh (hKH hk)
  change ((g:G) * k * (g:G)⁻¹ * k⁻¹) * k ∈ H at hm
  change (g:G) * k * (g:G)⁻¹ ∈ H
  simpa only [inv_mul_cancel_right] using hm

/-- The same calculation gives the correct normalization of the inverse conjugate. -/
theorem le_normalizer_conjBy_inv_of_commute_image
    (P H K A : Subgroup G) (hKP : K ≤ P) (hKH : K ≤ H)
    (hHA : H ≤ normalizer (A:Set G))
    (f : P →* D) (hker : f.ker ≤ H.subgroupOf P)
    (g : P) (hc : ∀ k : K, Commute (f g) (f (inclusion hKP k))) :
    K ≤ normalizer (A.conjBy (g:G)⁻¹ : Set G) := by
  have hh := (conjBy_le_of_commute_image P H K hKP hKH f hker g hc).trans hHA
  have hm := map_mono (f := (MulAut.conj (g:G)⁻¹).toMonoidHom) hh
  change (K.conjBy (g:G)).conjBy (g:G)⁻¹ ≤ _ at hm
  rw [conjBy_inv] at hm
  exact hm.trans (A.le_normalizer_map (MulAut.conj (g:G)⁻¹).toMonoidHom)

end Subgroup
