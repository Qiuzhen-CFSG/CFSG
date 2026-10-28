module

public import Theory.GroupTheory.PerfectCentralCoverExistence
public import Mathlib.GroupTheory.Sylow

/-!
# Automorphism rigidity across a perfect central cover

An automorphism descends through a covering whose kernel is the center.
If it fixes a subgroup pointwise and its descended automorphism is conjugation
by an element of the image subgroup, lift that element to the original
subgroup. Uniqueness of maps from a perfect group to a central extension
identifies the original automorphism with this conjugation. Its conjugating
element lies in the subgroup center, so a central subgroup-center forces the
automorphism to be trivial.

This is the formal transfer step used in GLS, Volume 4, Chapter 4,
Lemma 2.8(c). Model-specific quotient automorphism and Sylow-center results
remain explicit inputs.
-/

namespace PerfectCentralCovering
variable {E B : Type*} [Group E] [Group B]

/-- Every automorphism descends through a covering with central kernel equal
to the whole center. The displayed equation records the actual projection. -/
public theorem Cover.exists_descended_aut (f : Cover E B)
    (hk : f.toMonoidHom.ker = Subgroup.center E) (α : MulAut E) :
    ∃ β : MulAut B, ∀ x, β (f.toMonoidHom x) = f.toMonoidHom (α x) := by
  let e := QuotientGroup.quotientKerEquivOfSurjective f.toMonoidHom f.surjective
  have hmap : f.toMonoidHom.ker.map α.toMonoidHom = f.toMonoidHom.ker := by
    rw [hk]
    exact Subgroup.characteristic_iff_map_eq.mp inferInstance α
  let γ := QuotientGroup.congr _ _ α hmap
  let β := (e.symm.trans γ).trans e
  refine ⟨β, ?_⟩
  intro x
  have he (x : E) : e (QuotientGroup.mk x) = f.toMonoidHom x := rfl
  change e (γ (e.symm (f.toMonoidHom x))) = f.toMonoidHom (α x)
  rw [← he x, e.symm_apply_apply]
  exact he (α x)

/-- Rigidity transfers from innerness on the quotient and a subgroup-center
calculation. This applies in particular to a Sylow subgroup. -/
public theorem Cover.fixing_eq_one_of_image_inner
    (f : Cover E B) (hk : f.toMonoidHom.ker = Subgroup.center E)
    (P : Subgroup E)
    (hcenter : (Subgroup.center P).map P.subtype ≤ f.toMonoidHom.ker)
    (hinner : ∀ β : MulAut B,
      (∀ b ∈ P.map f.toMonoidHom, β b = b) →
      ∃ b ∈ P.map f.toMonoidHom, β = MulAut.conj b)
    (α : MulAut E) (hfix : ∀ x ∈ P, α x = x) : α = 1 := by
  let := f.isPerfect
  obtain ⟨β, hβ⟩ := f.exists_descended_aut hk α
  have hfixβ : ∀ b ∈ P.map f.toMonoidHom, β b = b := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hβ, hfix x hx]
  obtain ⟨b, hb, heβ⟩ := hinner β hfixβ
  obtain ⟨x, hx, rfl⟩ := hb
  have he : α.toMonoidHom = (MulAut.conj x).toMonoidHom := by
    apply monoidHom_eq_of_isPerfect_of_comp_eq f.toMonoidHom f.ker_le_center
    ext y
    change f.toMonoidHom (α y) = f.toMonoidHom (x * y * x⁻¹)
    rw [← hβ, heβ, MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hxC : (⟨x, hx⟩ : P) ∈ Subgroup.center P := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hexy := DFunLike.congr_fun he (y : E)
    change α (y : E) = x * (y : E) * x⁻¹ at hexy
    rw [hfix y y.property] at hexy
    exact (mul_inv_eq_iff_eq_mul.mp hexy.symm).symm
  have hxZ := f.ker_le_center (hcenter (Subgroup.mem_map_of_mem P.subtype hxC))
  change x ∈ Subgroup.center E at hxZ
  ext y
  have hey := DFunLike.congr_fun he y
  change α y = x * y * x⁻¹ at hey
  change α y = y
  rw [hey, ← Subgroup.mem_center_iff.mp hxZ y, mul_inv_cancel_right]
end PerfectCentralCovering
