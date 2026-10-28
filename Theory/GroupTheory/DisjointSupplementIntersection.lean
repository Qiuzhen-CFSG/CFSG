module
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# A supplement to two disjoint subgroups

If A and B lie disjointly in R, and H misses R and is normalized by A and B,
then AH and BH meet in H. Consequently an invariant subgroup contained in AH
lies in H whenever an automorphism preserves R and H and moves A disjointly.
This is the central-supplement argument in Aschbacher–Smith 2.4.23(5).
-/

public section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G]
theorem sup_inf_sup_eq_of_disjoint_supplement
    (A B R H : Subgroup G) (hAR : A ≤ R) (hBR : B ≤ R)
    (hAB : Disjoint A B) (hRH : Disjoint R H)
    (hAH : A ≤ normalizer H) (hBH : B ≤ normalizer H) :
    (A ⊔ H) ⊓ (B ⊔ H) = H := by
  apply le_antisymm ?_ (le_inf le_sup_right le_sup_right)
  intro y hy
  have ha := hy.1
  have hb := hy.2
  change y ∈ (↑(A ⊔ H) : Set G) at ha
  rw [coe_mul_of_left_le_normalizer_right A H hAH] at ha
  change y ∈ (↑(B ⊔ H) : Set G) at hb
  rw [coe_mul_of_left_le_normalizer_right B H hBH] at hb
  obtain ⟨a,ha,h,hh,rfl⟩ := ha
  obtain ⟨b,hb,k,hk,he⟩ := hb
  change b*k=a*h at he
  change h∈H at hh
  have hR : a⁻¹*b∈R := R.mul_mem (R.inv_mem (hAR ha)) (hBR hb)
  have hH : a⁻¹*b∈H := by
    have he' : a⁻¹*b=h*k⁻¹ := by
      calc a⁻¹*b = a⁻¹*(b*k)*k⁻¹ := by simp only [mul_assoc,mul_inv_cancel,mul_one]
           _ = h*k⁻¹ := by rw [he,inv_mul_cancel_left]
    rw [he']
    exact H.mul_mem hh (H.inv_mem hk)
  have hab : a=b := by
    have hz : a⁻¹*b=1 := mem_bot.mp ((disjoint_iff.mp hRH) ▸ ⟨hR,hH⟩)
    exact (inv_mul_eq_one.mp hz)
  have ha1 : a=1 := mem_bot.mp ((disjoint_iff.mp hAB) ▸ ⟨ha,hab ▸ hb⟩)
  simpa only [ha1,one_mul] using hh

theorem le_supplement_of_invariant_disjoint_conjugate
    (N A R H : Subgroup G) (hNA : N≤A⊔H) (hAR : A≤R)
    (hRH : Disjoint R H) (hAH : A≤normalizer H)
    (e : G≃*G) (hN : N.map e.toMonoidHom=N)
    (hR : R.map e.toMonoidHom=R) (hH : H.map e.toMonoidHom=H)
    (hAA : Disjoint A (A.map e.toMonoidHom)) : N≤H := by
  have hNB := map_mono (f:=e.toMonoidHom) hNA
  rw [hN,map_sup,hH] at hNB
  have hBR : A.map e.toMonoidHom≤R := by
    simpa only [hR] using map_mono (f:=e.toMonoidHom) hAR
  have hBH : A.map e.toMonoidHom≤normalizer H := by
    rintro y ⟨a,ha,rfl⟩
    rw [mem_normalizer_iff_map_conj_eq]
    have h := mem_normalizer_iff_map_conj_eq.mp (hAH ha)
    rw [←hH,map_map]
    have he : (MulAut.conj (e a)).toMonoidHom.comp e.toMonoidHom =
        e.toMonoidHom.comp (MulAut.conj a).toMonoidHom := by ext t;simp
    change H.map ((MulAut.conj (e a)).toMonoidHom.comp e.toMonoidHom)=H.map e.toMonoidHom
    rw [he,←map_map]
    change (H.map (↑(MulAut.conj a))).map e.toMonoidHom=H.map e.toMonoidHom
    rw [h]
  exact (le_inf hNA hNB).trans_eq
    (sup_inf_sup_eq_of_disjoint_supplement A (A.map e.toMonoidHom) R H
      hAR hBR hAA hRH hAH hBH)
end Subgroup
